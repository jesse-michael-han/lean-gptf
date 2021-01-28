import tactic.gptf
import data.list.sigma

section gptf

example {α} (a : α) : a = a :=
begin
  refl
end

example : ∃ n : ℕ, 8 = 2*n :=
begin
  exact dec_trivial
end

example {P Q R : Prop} : P → (P → R) → R :=
begin
  intro h1, exact λ h2, h2 h1
end

example {p q r : Prop} (h₁ : p) (h₂ : q) : (p ∧ q) ∨ r :=
begin
  exact or.inl ⟨h₁, h₂⟩
end

example {P Q : Prop} : (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
begin
  rintro ⟨h₁, h₂⟩, simp [h₁, h₂]
end

example {P Q R : Prop} : (P ∧ Q) → ((P → R) → ¬ (Q → ¬ R)) :=
begin
  rintro ⟨h₁, h₂⟩ h₃, apply not_imp_of_and_not, apply and.intro h₂,
  rw [not_not], apply h₃ h₁
end

example (n : ℕ) (m : ℕ) : nat.succ n < nat.succ n + 1  :=
begin
  rw [lt_add_iff_pos_right], exact dec_trivial
end

example : ∀ (F1 F2 F3 : Prop), ((¬F1 ∧ F3) ∨ (F2 ∧ ¬F3)) → (F2 → F1) → (F2 → F3) →  ¬F2 :=
begin
  tauto
end

example : ∀ (f : nat → Prop), f 2 → ∃ x, f x :=
begin
  intros f hf, exact ⟨_, hf⟩
end

example {G} [group G] (x y z : G) : (x * z) * (z⁻¹ * y) = x * y :=
begin
  simp [mul_assoc]
end
universes u v

example {α : Type u} {β : α → Type v} [_inst_1 : decidable_eq α] {a : α} {l₁ l₂ : list (sigma β)} :
  (list.kerase a l₁).kunion (list.kerase a l₂) = list.kerase a (l₁.kunion l₂) :=
begin
  induction l₁ with x xs generalizing l₂; cases l₂ with y ys; simp
end

end gptf
