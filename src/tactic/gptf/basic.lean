import system.io
import tactic
import tactic.gptf.utils.util

meta structure ModelAPI (input_format : Type := json) : Type :=
(query : input_format → io json)

/- for testing -/
meta def dummy_api {α} : ModelAPI α :=
⟨λ _, pure $ json.of_string "[DummyAPI] FAILURE"⟩


meta structure BFSNode : Type :=
(state : tactic_state)
(score : ℤ := 0)
(tactics : list string := [])
(depth : ℕ := 0)

meta def BFSNode.to_json : BFSNode → json
| ⟨state, score, tacs, depth⟩ :=
json.object $
  [
      ("state", json.of_string $ (format.to_string ∘ has_to_format.to_format) state)
    , ("score", json.of_int score)
    , ("tactics", json.array $ json.of_string <$> tacs)
    , ("depth", json.of_int depth)
  ]

meta instance : has_to_tactic_json BFSNode :=
⟨pure ∘ BFSNode.to_json⟩

meta instance : has_to_format BFSNode :=
⟨has_to_format.to_format ∘ BFSNode.to_json⟩

namespace BFSNode

meta def of_current_state (score : ℤ := 0) (tacs : list string := []) : tactic BFSNode := do {
  ts ← tactic.read,
  pure $ ⟨ts, score, tacs, 0⟩
}

end BFSNode

section run_all_beam_candidates

meta def get_tac_and_capture_result (next_candidate : string) : tactic (tactic_result unit) := do {
  tac ← do {
    env ← tactic.get_env,
    eval_trace format!"[get_tac_and_capture_result] PARSING TACTIC: {next_candidate}",
    tac ← parse_itactic next_candidate,
    eval_trace format!"[get_tac_and_capture_result] PARSE SUCCESSFUL",
    tactic.set_env env,
    pure tac
  },
  eval_trace format!"[get_tac_and_capture_result] TRYING TACTIC: {next_candidate}",
  result ← tactic.capture' (tactic.try_for_time 10000 $ tactic.try_for 200000 tac), -- if `tac` fails, exception is captured here
  eval_trace format!"[get_tac_and_capture_result] RESULT: {result}",
  pure result
}

meta def try_get_tac_and_capture_result (tac_string : string) : tactic (tactic_result unit) := do {
  get_tac_and_capture_result tac_string <|> do {
    let msg : format := format!"[try_get_tac_and_capture_result] parse_itactic failed on {tac_string}",
    eval_trace msg,
    interaction_monad.mk_exception msg none <$> tactic.read
  }
}

/- TODO(jesse): since this is now used only for the interactive frontend,
   replace the inner loop with a `run_async <$> ...` -/
meta def run_all_beam_candidates
  (get_candidates : json → tactic (list (string × native.float)))
  (msg : json)
  : tactic (list (tactic_result unit × string × native.float) × list string) := do {

  let try_candidate_state := (list (string × native.float) × (list $ option $ tactic_result unit × string × native.float)),
  let stop : option (tactic_result unit × string × native.float) → state_t try_candidate_state tactic bool :=
    λ arg, match arg with
    | some ⟨result, candidate⟩ := do {
      state_t.lift result.is_done
    }
    | none := pure ff
    end,

  let try_candidate : state_t try_candidate_state tactic (option $ tactic_result unit × string × native.float) := do {
    state_t.lift $ eval_trace format!"[try_candidate] ENTERING",
    ts ← state_t.lift tactic.read,
    state_t.lift $ eval_trace format!"[try_candidate] READ TACTIC STATE",
    ⟨rest, _⟩ ← state_t.get,
    match rest with
    | [] := do {
      state_t.lift $ eval_trace format!"[try_candidate] END OF LOOP",
      pure $ some ⟨interaction_monad.fail "all candidates failed" ts, "FAILURE", 0.0⟩
    }
    | (next_candidate::candidates) := do  {
      state_t.modify (λ ⟨_, rs⟩, ⟨candidates, rs⟩),
      result ← monad_lift $ try_get_tac_and_capture_result next_candidate.fst,
      when (interaction_monad.result.is_success $ result) $
        state_t.modify $ λ ⟨candidates, rs⟩, ⟨candidates, rs ++ [some $ ⟨result, next_candidate⟩]⟩,
      state_t.lift $ eval_trace format!"[try_candidate] CAPTURED RESULT: {result}",
      pure $ some ⟨result, next_candidate⟩
    }
    end
  },

  -- this is responsible for gracefully handling "error" JSON messages and should return an empty list of candidates
  candidates ← list.filter (λ x, ¬ "tidy" ≤ prod.fst x) <$> (get_candidates msg >>= list.dedup'),

  eval_trace format!"[run_all_beam_candidates] CANDIDATES: {candidates}",
  successful_candidates ← (prod.snd <$> prod.snd <$> state_t.run (iterate_until try_candidate stop candidates.length $ pure none) ⟨candidates, []⟩),
  eval_trace format!"[run_all_beam_candidates] EXITING TRY_CANDIDATE LOOP",
  eval_trace format!"[run_all_beam_candidates] SUCCESSFUL CANDIDATES: {successful_candidates}",
  pure ⟨successful_candidates.filter_map id, prod.fst <$> candidates⟩
}

end run_all_beam_candidates
