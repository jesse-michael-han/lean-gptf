import tactic.gptf

example {α} (a : α) : a = a :=
begin
  refl
end

example : ∃ n : ℕ, 8 = 2*n :=
begin
  exact ⟨4, rfl⟩
end

example {P Q R : Prop} : P → (P → R) → R :=
begin
  intros hp₁ hp₂, exact hp₂ hp₁
end

example {p q r : Prop} (h₁ : p) (h₂ : q) : (p ∧ q) ∨ r :=
begin
  exact or.inl ⟨h₁, h₂⟩
end

example {P Q : Prop} : (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
begin
  intro h, simp [h]
end

example {P Q R : Prop} : (P ∧ Q) → ((P → R) → ¬ (Q → ¬ R)) :=
begin
  intros h1 h2, intro h3, apply h3 _, { cases h1 with p h1, exact h2 p }, intros, exact h1.right
end

example (n : ℕ) (m : ℕ) : nat.succ n < nat.succ n + 1  :=
begin
  exact lt_add_one _
end

