import tactic
import tactic.gptf.utils
import tactic.gptf.basic

namespace openai

section openai_api

meta structure CompletionRequest : Type :=
(prompt : string)
(max_tokens : int := 16)
(temperature : native.float := 1.0)
(top_p : native.float := 1)
(n : int := 1)
(best_of : option int := none)
(stream : option bool := none)
(logprobs : int := 0)
(echo : option bool := none)
(stop : option string := none) -- TODO(jesse): list string
(prompt_token := "TACTIC")
(prompt_prefix := "")
(replace_prefix : option (string → string) := none)

meta def CompletionRequest.to_tactic_json : CompletionRequest → tactic json :=
let validate_max_tokens : int → bool := λ n, n ≤ 4096 in
let validate_float_frac : native.float → bool := λ k, 0 ≤ k ∧ k ≤ 1 in
let validate_and_return {α} [has_to_format α] (pred : α → bool) : α → tactic α :=
  λ a, ((guard $ pred a) *> pure a <|>
    by {tactic.unfreeze_local_instances,
        exact (tactic.fail format!"[openai.CompletionRequest.to_tactic_json] VALIDATION FAILED FOR {a}")}) in
let validate_optional_and_return {α} [has_to_format α] (pred : α → bool) : option α → tactic (option α) := λ x, do {
  match x with
  | (some val) := some <$> by {tactic.unfreeze_local_instances, exact (validate_and_return pred val)}
  | none := pure none
  end
} in
let MAX_N : int := 128 in
λ req, match req with
| ⟨prompt, max_tokens, temperature, top_p, n, best_of,
  stream, logprobs, echo, stop, prompt_token, prompt_prefix, replace_prefix⟩ := do
  -- TODO(jesse): ensure validation does not fail silently
  max_tokens ← validate_and_return validate_max_tokens max_tokens,
  -- temperature ← validate_and_return validate_float_frac temperature,
  top_p ← validate_and_return validate_float_frac top_p,
  n ← validate_and_return (λ x, 0 ≤ x ∧ x ≤ MAX_N) /- go wild with the candidates -/ n,
  best_of ← validate_optional_and_return (λ x, n ≤ x ∧ x ≤ MAX_N) best_of,

  -- tactic.trace $ "[openai.CompletionRequest.to_tactic_json] VALIDATION PASSED",

  let pre_kvs : list (string × option json) := [
    ("prompt", json.of_string prompt),
    ("max_tokens", json.of_int max_tokens),
    ("temperature", json.of_float temperature),
    ("top_p", json.of_float top_p),
    ("n", json.of_int n),
    ("best_of", json.of_int <$> best_of),
    ("stream", json.of_bool <$> stream),
    ("logprobs", some $ json.of_int logprobs),
    ("echo", json.of_bool <$> echo),
    ("stop", json.of_string <$> stop)
  ],

  pure $ json.object $ pre_kvs.filter_map (λ ⟨k,mv⟩, prod.mk k <$> mv)
end

meta def CompletionRequest.to_cmd
  (engine_id : string)
  (api_key : string) :
  CompletionRequest → io (io.process.spawn_args)
| req@⟨prompt, max_tokens, temperature, top_p, n, best_of,
  stream, logprobs, echo, stop, prompt_token, prompt_prefix, replace_prefix⟩ := do
-- io.put_str_ln' format!"[openai.CompletionRequest.to_cmd] ENTERING",
serialized_req ← io.run_tactic' $ req.to_tactic_json,
-- io.put_str_ln' format!"[openai.CompletionRequest.to_cmd] SERIALIZED",
win ← io.run_tactic is_windows,
pure {
  cmd := "curl",
  args := [
         "--silent"
      ,  " -N"
      -- ,  "-u"
      -- , format.to_string $ format!":{api_key}"
      ,  "-X"
      , "POST"
      ,  format.to_string format!"http://api-{engine_id}.spolu.svc.owl.sci.openai.org:5001/v1/engines/dummy/completions"
      , "-H", "OpenAI-Organization: openai"
      , "-H", "Content-Type: application/json"
      , "-H", "Authorization: Bearer dummy"
      , "-d"
      , let jr := json.unparse serialized_req in if win then
          "\\\"".intercalate (jr.split (= '\"'))
        else
          jr
    ]
}

meta def serialize_ts
  (req : CompletionRequest)
  : tactic_state → tactic CompletionRequest := λ ts, do {
  ts_str ← postprocess_tactic_state ts,
  decl_name ← postprocess_decl_name,

  let prompt : string :=
    (format!"LEAN3 DECL {decl_name} OPENS  GOAL {ts_str} OUTCOME proved {req.prompt_token}").to_string,
  let prompt := if req.prompt_prefix.length > 0 then
    (format!"{prompt} {req.prompt_prefix}").to_string
  else
    prompt,

  -- tactic.trace format!"\n===================\nPROMPT: {prompt}\n===================\n",

  pure {
    prompt := prompt,
    ..req
  }
}

setup_tactic_parser

private meta def decode_response_msg : json → io (json × json) := λ response_msg, do {
  (json.array choices) ← 
    option.to_monad $ response_msg.lookup "choices" | 
    io.fail' format!"can't find choices in {response_msg}",
  prod.mk <$> (json.array <$> choices.mmap (λ choice, option.to_monad $ json.lookup choice "text")) <*> do {
    logprobss ← choices.mmap (λ msg, option.to_monad $ msg.lookup "logprobs"),
    scoress ← logprobss.mmap (λ logprobs, option.to_monad $ logprobs.lookup "token_logprobs"),
    result ← json.array <$> scoress.mmap (option.to_monad ∘ json_float_array_sum),
    pure result
  }
}

meta def openai_api (engine_id : string) (api_key : string) : ModelAPI CompletionRequest :=
let fn : CompletionRequest → io json := λ req, do {
  proc_cmds ← req.to_cmd engine_id api_key,
  response_raw ← io.cmd proc_cmds,
  -- io.put_str_ln' format!"[openai_api] RAW RESPONSE: {response_raw}",

  response_msg ←
    (option.to_monad $ json.parse response_raw) |
    io.fail' format!"[openai_api] JSON PARSE FAILED {response_raw}",

  -- io.put_str_ln' format!"GOT RESPONSE_MSG",

  do {
    predictions ←
      decode_response_msg response_msg | 
      io.fail' format!"[openai_api] UNEXPECTED RESPONSE MSG: {response_msg}",
    -- io.put_str_ln' format!"PREDICTIONS: {predictions}",
    pure (json.array [predictions.fst, predictions.snd])
  } <|> pure (json.array $ [json.of_string $ format.to_string $ format!"ERROR {response_msg}"])
} in ⟨fn⟩

end openai_api

section openai_proof_search

meta def read_first_line : string → io string := λ path, do
  buffer.to_string <$> (io.mk_file_handle path io.mode.read >>= io.fs.get_line)

meta def default_partial_req : openai.CompletionRequest :=
{
  prompt := "",
  max_tokens := 128,
  temperature := (1.0 : native.float),
  top_p := 1,
  n := 1,
  best_of := none,
  stream := none,
  logprobs := 0,
  echo := none,
  stop := "RESULT" -- TODO(jesse): list string,
}

meta def proof_search_step
  {input_format}
  (api : ModelAPI input_format)
  (serialize_ts : tactic_state → tactic input_format)
  (decode_response : json → tactic (list (tactic_result unit × string × native.float) × list string))
  : tactic (list string × list string) := do {
  serialized_ts ← tactic.read >>= serialize_ts,
  response_msg ← tactic.unsafe_run_io $ api.query serialized_ts,
  ⟨successes, candidates⟩ ← decode_response response_msg,
  pure $ flip prod.mk candidates $ successes.map (prod.fst ∘ prod.snd)
}

meta def gptf_proof_search_step
  (engine_id : string)
  (api_key : string)
  (req : CompletionRequest) :
  tactic (list string × list string) := do {
  proof_search_step
    (openai_api
      engine_id api_key)
        (serialize_ts req)
          (run_all_beam_candidates $ 
            unwrap_lm_response_logprobs req.prompt_prefix req.replace_prefix "[gptf_proof_search_step]")
}

end openai_proof_search

end openai
