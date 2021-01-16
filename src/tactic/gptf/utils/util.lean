import system.io
import tactic

section string

namespace string

def replace_char : string → char → char → string
| ⟨cs⟩ c₁ c₂ := ⟨cs.map (λ c, if c = c₁ then c₂ else c)⟩

end string

end string

namespace io

meta def fail' {α} (fmt : format) : io α := io.fail $ format.to_string fmt

meta def put_str_ln' : Π (fmt : format), io unit := io.put_str_ln ∘ format.to_string

end io

section io
open interaction_monad interaction_monad.result
namespace io

/-- verion of io.run_tactic' which does not suppress the exception msg -/
meta def run_tactic' {α} (tac :tactic α) : io α := do {
  io.run_tactic $ do {
    result ← tactic.capture tac,
    match result with
    | (success val _) := pure val
    | (exception m_fmt pos _) := do {
      let fmt_msg := (m_fmt.get_or_else (λ _, format!"none")) (),
      let msg := format!"[io.run_tactic'] {pos}: tactic failed\n-------\n{fmt_msg}\n-------\n",
      tactic.trace msg,
      tactic.fail msg
    }
    end
  }
}

end io
end io

section tactic_state
open interaction_monad.result
setup_tactic_parser

meta def num_goals' : tactic_state → option ℕ :=
λ ts, match tactic.num_goals ts with | (success val _) := pure val | _ := none end

-- TODO(jesse): this is a hack. might be better to do this in python
meta def consume_with_parser {α} (p : lean.parser α) : string → io string := λ inp, do {
  io.run_tactic' $ do
    prod.snd <$> (lean.parser.run (with_input p inp) "")
}

-- TODO(jesse): performance
meta def consume_spaces : string → string
| arg@⟨[]⟩ := arg
| arg@⟨(x::xs)⟩ := if x = ' ' then consume_spaces ⟨xs⟩ else arg

-- WARNING: this is a hack
meta def remove_indents_with_split (c : char := '\t'): string → string := λ str,
let strs := str.split (= '\t') in
string.intercalate (⟨['\t']⟩ : string) (consume_spaces <$> strs)

meta def postprocess_tactic_state : tactic_state → tactic string := λ ts, do
  let main : tactic string := do {
    let ts_str := ts.to_format.to_string,
    tabbed_ts_str ← do {
      if (num_goals' ts).get_or_else 0 ≤ 1
      then pure $ ts_str.replace_char '\n' '\t'
      else tactic.unsafe_run_io $ (λ x, string.replace_char x '\n' '\t')
             <$> (consume_with_parser small_nat >=>
               consume_with_parser ident) ts_str},
    pure $ remove_indents_with_split '\t' tabbed_ts_str
  },
  main <|> (let msg := "[postprocess_tactic_state] WARNING: POSTPROCESSING FAILED" in
    tactic.trace msg *> tactic.fail msg)

end tactic_state

section json

section has_to_json
universe u

meta class has_to_json (α : Type u) : Type (u+1) :=
(to_json : α → json)

meta class has_to_tactic_json (α : Type u) : Type (u+1) :=
(to_tactic_json : α → tactic json)

meta class has_from_json (α : Type u) : Type (u+1) :=
(from_json : json → tactic α)

end has_to_json

meta def list.lookup_prod {α β} : (list (α × β)) → (α → bool) → option β
| [] _ := none
| (⟨a,b⟩::xs) p := if p a then pure b else xs.lookup_prod p

meta def json.get_string : json → option string
| (json.of_string str) := pure str
| _ := none

meta def json.get_float : json → option native.float
| (json.of_float str) := pure str
| _ := none

meta def json.lookup : json → string → option json
| (json.object kvs) str := kvs.lookup_prod $ λ k, k = str
| _ _ := none

end json

meta def json_float_array_sum : json → option json
| (json.array xs) := json.of_float <$> xs.mfoldr (λ msg acc, match msg with
  | (json.of_float val) := pure $ acc + val
  | (json.of_int val) := pure $ acc + native.float.of_int val
  | exc := none
  end) (0.0 : native.float)
| exc := none

meta def unwrap_lm_response_logprobs (ident : option string) : json → tactic (list $ string × native.float)
| (json.array $ [(json.array predictions), (json.array scores)]) := do {
  decoded_strings ← predictions.mmap $ option.to_monad ∘ json.get_string,
  decoded_scores ← scores.mmap $ option.to_monad ∘ json.get_float,
  pure $ list.zip decoded_strings decoded_scores
}
| exc := tactic.trace format!"{ident.get_or_else \"[unwrap_lm_response_logprobs.anonymous]\"} run_best_beam_candidate UNEXPECTED MESSAGE:\n---\n{exc}\n---\n" *> pure []

meta def format.join_using : format → list format → format := λ x xs,
format.join $ list.intercalate [x] (pure <$> xs)

section json

-- for debugging

meta def json.compare : Π (x y : json), bool
| (json.of_string s) (json.of_string s') := s = s'
| (json.of_int k) (json.of_int k') := k = k'
| (json.of_float x) (json.of_float x') := x = x' -- might have to make this tt
| (json.of_bool b) (json.of_bool b') := b = b'
| (json.null) (json.null) := tt
| (json.object kvs) (json.object kvs') := (list.zip kvs kvs').foldr
  (λ ⟨⟨k₁, v₁⟩, ⟨k₂, v₂⟩⟩ acc,
  json.compare k₁ k₂ && json.compare v₁ v₂ && acc) tt
| (json.array args) (json.array args') := (list.zip args args').foldr
  (λ ⟨j₁, j₂⟩ acc, acc && json.compare j₁ j₂) tt
| _ _ := ff

meta def json.to_raw_fmt : json → format
| (json.of_string s) := format!"(json.of_string \"{s}\")"
| (json.of_int k) := format!"(json.of_int {k})"
| (json.of_float x) := format!"(json.of_float {x})"
| (json.of_bool b) := format!"(json.of_bool {b})"
| (json.null) := "(json.null)"
| (json.object kvs) := let f : string × json → format :=
  (λ ⟨k,v⟩, json.to_raw_fmt k ++ " : " ++ json.to_raw_fmt v) in
   format!"(json.object " ++ format.join_using " " (f <$> kvs) ++ ")"
| (json.array args) := "(json.array " ++ format.join_using " " (json.to_raw_fmt <$> args) ++ ")"

end json

meta def tactic_state.is_done (state : tactic_state) : tactic bool := do {
  ts ← tactic.read,
  result ← do {
    tactic.write state,
    (tactic.done *> pure tt) <|> pure ff
  },
  tactic.write ts,
  pure result
}

meta def tactic_result.is_done {α} (tr : tactic_result α) : tactic bool := do {
  match tr with
  | (interaction_monad.result.success val state) := state.is_done
  | (interaction_monad.result.exception _ _ _) := pure ff
  end
}

section interaction_monad

meta def interaction_monad.result.is_success {σ α} : interaction_monad.result σ α → bool := λ x,
match x with | (interaction_monad.result.success _ _) := tt | _ := ff end

end interaction_monad

section run_with_state'

declare_trace gptf

meta def set_show_eval_trace : bool → tactic unit := tactic.set_bool_option `evaltrace

meta def eval_trace {α} [has_to_tactic_format α] : α → tactic unit | a := do {
  when (tactic.is_trace_enabled_for `gptf) (tactic.trace a)
}

namespace interaction_monad
open interaction_monad.result
meta def run_with_state' {σ₁ σ₂ : Type} {α : Type*} (state : σ₁) (tac : interaction_monad σ₁ α) : interaction_monad σ₂ α :=
λ s, match (tac state) with
     | (success val _) := success val s
     | (exception fn pos _) := exception fn pos s
     end
end interaction_monad
end run_with_state'

section list -- WARNING: hack

local notation `α` := string

meta structure dedup_state' : Type :=
(seen : native.rb_map α native.float := native.mk_rb_map)
(result : list (α) := [])

local notation `m` := tactic
meta def dedup_list_aux' : list (α × native.float) → state_t dedup_state' m unit
| [] := pure ()
| (x::xs) := do {
  σ ← get,
  if (σ.seen.contains x.1) then (do
    (some old_score) ← (pure $ σ.seen.find x.1) | state_t.lift tactic.failed,
    let new_seen := if x.2 > old_score then (σ.seen.erase x.1).insert x.1 x.2 else σ.seen,
    modify $ λ σ, dedup_state'.mk new_seen (σ.result),
    dedup_list_aux' xs)
    else do
    modify $ λ σ, dedup_state'.mk (σ.seen.insert x.1 x.2) (σ.result ++ [x.1]),
    dedup_list_aux' xs
}

meta def list.dedup' : list (α × native.float) → m (list $ α × native.float) := λ xs, do
  σ ← prod.snd <$> state_t.run (dedup_list_aux' xs) {},
  σ.result.mmap (λ x, do { prod.mk x <$> σ.seen.find x })

end list

section iterate_until

meta def iterate_until_aux
  {m} [monad m] [alternative m] {α}
  (tac :  m α) (stop : α → m bool) (fuel_exhausted_callback : m α)
  : Π (fuel : ℕ), m α
| 0 := do {result ← tac, mcond (stop result) (pure result) fuel_exhausted_callback}
| (n+1) := do { result ← tac, mcond (stop result) (pure result) (iterate_until_aux n)}

meta def iterate_until
  {m} [monad m] [alternative m] {α}
  (tac : m α) (stop : α → m bool) (fuel := 100000)
  (fuel_exhausted_callback : m α := alternative.failure)
  : m α
  :=
iterate_until_aux tac stop fuel_exhausted_callback fuel

end iterate_until

namespace tactic

open interaction_monad.result
meta def run (tac : tactic unit) : tactic (interaction_monad.result tactic_state unit) := do {
  σ ← get_state,
  match tac σ with
  | r@(success _ new_state) := interaction_monad.set_state new_state *> pure r
  | r@(exception fn pos new_state) := pure r
  end
}

meta instance has_to_format_tactic_result {α : Type*} [has_to_format α] : has_to_format (interaction_monad.result tactic_state α) :=
⟨λ r,
  match r with
  | (success val new_state) := format!"SUCCESS!\nNEW_STATE: {new_state}\nVAL: {val}"
  | (exception fn pos old_state) := do {
    let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
    format!"EXCEPTION!\nMSG: {msg}\nPOS: {pos}\nOLD_STATE: {old_state}"
  }
  end
⟩

meta instance has_to_tactic_format_tactic_result {α : Type*} [has_to_format α] : has_to_tactic_format (interaction_monad.result tactic_state α) :=
⟨λ σ, pure $ has_to_format.to_format σ⟩

/-- Prints a 'Try this:' message. -/
meta def trythis : string → tactic unit
| s := tactic.trace (sformat!"Try this: {s}")

end tactic

meta def serialize_list_string : list string → json := λ xs,
  json.array $ json.of_string <$> xs

meta def score_of_float : native.float → int :=
λ x, native.float.floor ((1000.0 : native.float) * x)

namespace tactic
open interaction_monad interaction_monad.result

/- capture but backtrack the state -/
meta def capture' {α} (t : tactic α) : tactic (tactic_result α) :=
λ s, match t s with
| (success r s') := success (success r s') s
| (exception f p s') := success (exception f p s') s
end

end tactic

section parse_tac

setup_tactic_parser

open tactic

/-- Parse a reflected interactive tactic from a string.
    The result can be evaluated to a `tactic unit` by using
    `eval_expr (tactic unit)`. -/
meta def parse_itactic_reflected (tactic_string : string) : tactic expr :=
let itactic_string := "{ " ++ tactic_string ++  " }" in
flip lean.parser.run "" $ do
  get_state >>= λ ps, of_tactic $ do
    tactic.set_env ps.env,
    eval_trace format!"[parse_itactic_reflected] TRYING TO PARSE {itactic_string}",
    (reflected_value.expr ∘ prod.fst) <$>
      (@interaction_monad.run_with_state' parser_state _ _ ps $
        with_input parser.itactic_reflected itactic_string)

/-- Parse an interactive tactic from a string. -/
meta def parse_itactic (tactic_string : string) : tactic (tactic unit) := do
  rtac ← parse_itactic_reflected tactic_string,
  eval_expr (tactic unit) rtac

end parse_tac
