# lean-gptf

This repository lets you use GPTf to suggest tactics based on the goal state.

# Accessing the OpenAI API

GPTf is a cloud service provided by OpenAI.
Suggestions are computed by polling this service, and this requires getting an access token from OpenAI.
{here are the ways of getting access tokens}

Once you have recieved an accesss token, either add it as an OS environment variable called `OPENAI_API_KEY`

```
# ~/.zshenv
export OPENAI_API_KEY=<key goes here>
```

You may have to log out and back in to get this to work.

__or__ you can paste the key directly in to the lean document:

```
example goes here
```

but remember not to commit your key to source control!

# Usage

```
import gptf

lemma my_lemma : a = b :=
begin
  gpt -- this will poll the server and return a set of 'try this' commands.
end

```

## Options

- `fuel`
- best-first vs greedy-search
- temperature
- numebr of suggestions to return
- turn on logging

## Considerations

Remember that each poll to the server costs 'tokens'. At the time of writing, each request costs around $0.xx.
So when using this tactic try to avoid editing the lean document above the point at which `gpt` is invoked, because each edit will cause the server to be polled, draining credit.

Also remember that even if the system doesn't progress the goal, you may be able to see clues of how to progress by looking at the suggestions which fail given in the 'Predictions' list.



