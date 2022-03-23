/- Author: E.W.Ayers © 2019.

Some helpers for dealing with monads etc.
-/
namespace interaction_monad

namespace result

  variables {σ α β : Type}

  protected meta def map (f : α → β) : interaction_monad.result σ α → interaction_monad.result σ β
  | (success b s) := success (f b) s
  | (exception m p s) := exception m p s

  meta def map_state {τ : Type} (f : σ → τ) : result σ α → result τ α
  | (success a s) := success a (f s)
  | (exception m p s) := exception m p (f s)

  meta def state : result σ α → σ
  | (success b s) := s
  | (exception m p s) := s

  meta def get : result σ α → option α
  | (success b _) := some b
  | (exception _ _ _) := none

  meta def as_success : result σ α → option (α × σ)
  | (success b s) := some (b,s)
  | _ := none

  meta def as_exception : result σ α → option (option (unit → format) × option pos × σ)
  | (success b s) := none
  | (exception m p s) := (m,p,s)

  meta def as_except : result σ α → except (option (unit → format) × option pos) α
  | (success b s) := except.ok b
  | (exception m p s) := except.error $ (m, p)

  meta instance {σ} : functor (result σ) := {map := @result.map σ}

end result

end interaction_monad
