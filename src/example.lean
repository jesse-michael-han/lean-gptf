import tactic.gptf

example {α} (a : α) : a = a :=
begin
  refl
end

example : ∃ n : ℕ, 8 = 2*n :=
begin
  exact ⟨4, by norm_num⟩
end

example {P Q R : Prop} : P → (P → R) → R :=
begin
  tauto
end

example {p q r : Prop} (h₁ : p) (h₂ : q) : (p ∧ q) ∨ r :=
begin
  exact or.inl ⟨h₁, h₂⟩
end

example {P Q : Prop} : (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
begin
  rintro ⟨hp, hq⟩, rw not_or_distrib, exact ⟨hp, hq⟩
end

example {P Q R : Prop} : (P ∧ Q) → ((P → R) → ¬ (Q → ¬ R)) :=
begin
  rintros ⟨h₁, h₂⟩ h₃, simp [@h₂], exact h₃ h₁
end

example (n : ℕ) (m : ℕ) : nat.succ n < nat.succ n + 1  :=
begin
  apply nat.lt_succ_self
end
