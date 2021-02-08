import tactic.gptf.basic
import tactic.gptf.backends.openai
import tactic.gptf.utils.util
import tactic.gptf.gptf
import tactic.finish

open openai

namespace tactic

meta def autoname_core (e : expr) (cfg : interactive.GPTSuggestConfig := {}) : tactic (list name) := do {
  let cfg := {prompt_token := "PREDICTNAME", ..cfg},
  let req := {
    n := cfg.n,
    temperature := cfg.temp,
    prompt_token := cfg.prompt_token,
    prompt_prefix := cfg.pfx,
    replace_prefix := cfg.postprocess,
    .. default_partial_req
  },
  api_key ← get_openai_api_key,
  completion_request ← (autoname_serialize_ts_core e req),
  response_msg ← tactic.unsafe_run_io $ (openai_api cfg.engine_id api_key).query completion_request,
  responses ← list.map prod.fst <$>
    ((list.qsort (λ x y : string × native.float, prod.snd x > prod.snd y) <$>
      unwrap_lm_response_logprobs "" none "autonamer" response_msg) >>= list.dedup'),
  eval_trace format! "[autoname_core] RESPONSES: {responses}",
  list.filter_map id <$>
    responses.mmap (λ x, (optional $ lean.parser.run $ prod.fst <$>
      lean.parser.with_input lean.parser.ident x))
}

namespace interactive

meta def autoname (cfg : GPTSuggestConfig := {n := 12, temp := 1.0}) : tactic unit := do {
  ts ← tactic.read,
  e ← ts.fully_qualified >>= λ x, do {
    tactic.write x,
    extract_fully_bound_goal
  },
  tactic.pp e >>= λ e, tactic.trace format! "[autoname] Suggested names for goal\n------\n{e}\n------\n",
  tactic.write ts,
  nms ← autoname_core e cfg,
  nms.mmap' $ λ nm,
  tactic.trythis nm.to_string
}

end interactive
end tactic
