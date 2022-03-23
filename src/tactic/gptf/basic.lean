/-
Copyright (c) 2021 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han, Ed Ayers

Core logic of the `gptf` tactic
-/

import system.io
import tactic
import tactic.gptf.utils.util
import basic.control

meta structure ModelAPI (input_format : Type := json) : Type :=
(query : input_format → io json)

/- for testing -/
meta def dummy_api {α} : ModelAPI α :=
⟨λ _, pure $ json.of_string "[DummyAPI] FAILURE"⟩

section run_all_beam_candidates

meta def get_tac_and_capture_result (next_candidate : string) (timeout : ℕ := 5000) : tactic (tactic_result _) := do {
  tac ← do {
    env ← tactic.get_env,
    eval_trace format!"[get_tac_and_capture_result] PARSING TACTIC: {next_candidate}",
    tac ← parse_itactic next_candidate,
    eval_trace format!"[get_tac_and_capture_result] PARSE SUCCESSFUL",
    tactic.set_env env,
    pure tac
  },
  eval_trace format!"[get_tac_and_capture_result] TRYING TACTIC: {next_candidate}",
  result ← tactic.capture' (tactic.try_for_time timeout $ tactic.try_for 200000 tac), -- if `tac` fails, exception is captured here
  eval_trace format!"[get_tac_and_capture_result] RESULT: {result}",
  pure result
}

/-- This takes a 'next_candidate' object and then if the tactic result is a success then it will
update the candidate name to reflect the result it returned. -/
-- private meta def candidate_modify : (string) → tactic_result string → (tactic_result unit) × (string) :=
-- λ s r, ⟨r.map (λ _, ()), s <| r.get⟩

meta def try_get_tac_and_capture_result (tac_string : string) (timeout : ℕ := 5000) : tactic ((tactic_result unit) × string) := do {
  result_with_string ← get_tac_and_capture_result tac_string timeout <|> do {
    let msg : format := format!"[try_get_tac_and_capture_result] parse_itactic failed on {tac_string}",
    eval_trace msg,
    interaction_monad.mk_exception msg none <$> tactic.read
  },
  
  let candidate_modify : string → tactic_result string → ((tactic_result unit) × string) :=
    λ s r, ⟨r.map $ (λ _, ()), s <| r.get⟩,
  pure $ candidate_modify tac_string result_with_string
}

meta def run_all_beam_candidates
  (get_candidates : json → tactic (list (string × native.float)))
  (msg : json)
  : tactic (list (tactic_result unit × string × native.float) × list string) := do {

  let find_successful_candidates
    (candidates : list (string × native.float))
    : tactic (list (tactic_result unit × string × native.float)) := do {
    tasks ← candidates.mmap (λ arg, flip prod.mk arg <$> tactic.run_async (try_get_tac_and_capture_result arg.fst : tactic $ tactic_result unit × string)),
    tactic.using_new_ref ff $ λ flag, do
    tasks.iterM [] $ λ acc ⟨task, tac_string, score⟩, do {
      mcond (tactic.read_ref flag) (pure acc) $ do {
        let ⟨result, new_tac_string⟩ := task.get,
        if (interaction_monad.result.is_success result) then do {
          whenM (result.is_done) $ tactic.write_ref flag tt,
          pure $ acc ++ [⟨result, new_tac_string, score⟩]
        } else do {
          pure acc
        }
      }
    }
  },

  -- this is responsible for gracefully handling "error" JSON messages and should return an empty list of candidates
  candidates ← list.filter (λ x, not $ "tidy".is_prefix_of $ prod.fst x) <$> (get_candidates msg >>= list.dedup'),

  eval_trace format!"[run_all_beam_candidates] CANDIDATES: {candidates}",

  -- successful_candidates ← (prod.snd <$> prod.snd <$> state_t.run (iterate_until try_candidate stop candidates.length $ pure none) ⟨candidates, []⟩),
  successful_candidates ← (list.map pure) <$> (get_candidates msg >>= list.dedup' >>= find_successful_candidates),

  eval_trace format!"[run_all_beam_candidates] EXITING TRY_CANDIDATE LOOP",
  eval_trace format!"[run_all_beam_candidates] SUCCESSFUL CANDIDATES: {successful_candidates}",
  pure ⟨successful_candidates.filter_map id, prod.fst <$> candidates⟩
}



end run_all_beam_candidates
