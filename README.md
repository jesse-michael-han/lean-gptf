# lean-gptf

This repository lets you use GPTf to suggest tactics based on the goal state.

# Setup

We are currently using a fork of Lean 3.23c. We will use an official release in the near future.

```
# download pre-built binaries and build the project
leanpkg configure && leanpkg build
```

After Lean is finished compiling, try commenting out the proofs in `src/example.lean` and calling `gptf` inside the `begin ... end` blocks. Make sure your API key is set up (see below). For example,

```
example {α} (a : α) : a = a :=
begin
  gptf,
end
```

should succeed with a message like this:

```
Successes:
----------
Try this:  refl

All predictions:
----------------
Try this:  refl
```

# Accessing the OpenAI API

GPT-f is a generative language model trained by OpenAI. It is available over the OpenAI API using an API key. It receives a formatted tactic state as a prompt and will emit a list of tactics to try. The `gptf` tactic will try these tactics and return the ones that succeed as `Try this: ...` suggestions.

To get an API key, apply to join the beta here: https://bit.ly/3nNWMyB

Once you have recieved an API key, either add it as an OS environment variable called `OPENAI_API_KEY`

```
# ~/.zshenv, /etc/environment, etc.
export OPENAI_API_KEY=<key goes here> # you may have to log out and back in to get this to work
```

__or__ you can paste the key directly in to the Lean document:

```
-- located in ./src/tactic/gptf/gptf.lean

/- set to `some $KEY` if you don't want to mess with environment variables
   WARNING: do _not_ leave your key in committed source code -/
   private meta def OPENAI_API_KEY : option string := none
```

# Usage

```
import tactic.gptf

lemma my_lemma {α} (a : α) : a = a :=
begin
  gptf {n := 32, temp := 1.0} -- this will query the server and return a set of 'try this' commands.
end

```

## Options

- `temperature`: Controls the randomness of the predictions; defaults to 1.0. Decrease to make the model's predictions more deterministic.
- `n`: Number of predictions to try at once.

## Considerations

The `gptf` tactic will query a model via the OpenAI API using `curl`. This query will be re-executed every time Lean compiles the tactic, and will count towards your API key rate limit. Thus, to avoid hitting the rate-limit and being throttled, please:
- try not to have more than one uncommented `gptf` in a live Lean file at a time
- replace calls to `gptf` by successful predictions whenever possible

Also remember that even if the system doesn't progress the goal, you may be able to see clues of how to progress by looking at the suggestions which fail given in the 'Predictions' list. Currently, the model tends to predict long chains of rewrites; often, the first few rewrites in the chain will succeed.
