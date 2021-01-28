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
  apply nat.lt_succ_self
end

example : ∀ (F1 F2 F3 : Prop), ((¬F1 ∧ F3) ∨ (F2 ∧ ¬F3)) → (F2 → F1) → (F2 → F3) →  ¬F2 :=
begin
  tauto
end

example : ∀ (f : nat → Prop), f 2 → ∃ x, f x :=
begin
  exact λ f hf, Exists.intro 2 hf
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

section gptf_exact

example {α} (a : α) : a = a :=
begin
  exact (rfl)
end

example : ∃ n : ℕ, 8 = 2*n :=
begin
  exact (of_as_true trivial)
end

example {P Q R : Prop} : P → (P → R) → R :=
begin
  exact (λ (h1 : P) (h2 : P → R), h2 h1)
end

example {p q r : Prop} (h₁ : p) (h₂ : q) : (p ∧ q) ∨ r :=
begin
  exact (or.inl ⟨h₁, h₂⟩)
end

example {P Q : Prop} : (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
begin
  exact (not_or_distrib.mpr)
end

example {P Q R : Prop} : (P ∧ Q) → ((P → R) → ¬ (Q → ¬ R)) :=
begin
  refine (λ (h₁ : P ∧ Q) (h₂ : P → R), _),
  intro h₃, apply h₃ h₁.2, exact (h₂ h₁.left)
end

example (n : ℕ) (m : ℕ) : nat.succ n < nat.succ n + 1  :=
begin
  exact (nat.lt_succ_iff.mpr n.lt_succ_self)
end

example : ∀ (F1 F2 F3 : Prop), ((¬F1 ∧ F3) ∨ (F2 ∧ ¬F3)) → (F2 → F1) → (F2 → F3) →  ¬F2 :=
begin
  tauto
end

example : ∀ (f : nat → Prop), f 2 → ∃ x, f x :=
begin
  exact (λ (f : ℕ → Prop) (h : f 2), Exists.intro 2 h)
end

example {G} [group G] (x y z : G) : (x * z) * (z⁻¹ * y) = x * y :=
begin
  simp [mul_assoc]
end
universes u v

example {α : Type u} {β : α → Type v} [_inst_1 : decidable_eq α] {a : α} {l₁ l₂ : list (sigma β)} :
  (list.kerase a l₁).kunion (list.kerase a l₂) = list.kerase a (l₁.kunion l₂) :=
begin
  exact (list.kunion_kerase)
end

end gptf_exact
