import system.io
import tactic
import tactic.gptf.backends.openai

/-! A tactic that will ring up GPT to ask for help solving a goal.
  Remember to set the `OPEN_AI_KEY` environment variable.
  Eg:
  ```sh
  # ~/.zshenv
  export OPEN_AI_KEY="<PUT YOUR SECRET KEY IN HERE>"
  ```
  you may need to relogin to update.

  `n` is the number of iterations for the greedy search.
  `temperature` is a float between 0 and 1, and controls how deterministic the predictions are. -/

/- set to `some $KEY` if you don't want to mess with environment variables
   WARNING: do _not_ leave your key in committed source code -/
private meta def OPENAI_API_KEY : option string := none

meta def try_lookup_key (env : environment) : tactic string :=
↑OPENAI_API_KEY

meta def get_openai_api_key : tactic string := do {
  env ← tactic.get_env,
  (try_lookup_key env <|> (tactic.unsafe_run_io $ io.env.get "OPENAI_API_KEY") >>= option.to_monad) <|>
    tactic.fail "[get_openai_api_key] ERROR: can't find an OpenAI API key"
}
section gptf
namespace tactic
namespace interactive
setup_tactic_parser

open openai

meta structure GPTSuggestConfig : Type :=
(n : ℕ := 32)
(temp : native.float := 1.0)
(silent := ff)
(engine_id : string := "formal-large-lean-0119-mix-v1-c4")
(prompt_token := "PROOFSTEP")
(pfx := "")

meta def gptf_core (cfg : GPTSuggestConfig := {}) : tactic (list string × list string) := do {
tactic.success_if_fail done *> do {
  let req := { n := cfg.n, temperature := cfg.temp, prompt_token := cfg.prompt_token, prompt_prefix := cfg.pfx, .. default_partial_req },
  api_key ← get_openai_api_key,
  gptf_proof_search_step cfg.engine_id api_key req
  }
}

meta def gptf (cfg : GPTSuggestConfig := {}) : tactic unit := do {
  ⟨successes, predictions⟩ ← gptf_core cfg,
  if (successes.length > 0) then do {
    tactic.trace "\nSuccesses:\n----------",
    successes.mmap' tactic.trythis
  } else do {
    tactic.trace "no predictions succeeded"
  },
  when (predictions.length > 0) $
    tactic.trace "\nAll predictions: \n----------------" *> predictions.mmap' tactic.trythis
}

end interactive
end tactic

end gptf
