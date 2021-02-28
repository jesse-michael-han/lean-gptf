import tactic.gptf
import data.list.sigma

section gptf

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
  intro h1, exact λ h2, h2 h1
end

example {p q r : Prop} (h₁ : p) (h₂ : q) : (p ∧ q) ∨ r :=
begin
  exact or.inl ⟨h₁, h₂⟩
end

example {P Q : Prop} : (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
begin
  exact not_or_distrib.mpr -- `gptf {pfx := "exact"}`
end

example {P Q R : Prop} : (P ∧ Q) → ((P → R) → ¬ (Q → ¬ R)) :=
begin
  rintros ⟨h₁, h₂⟩ h₃, try {exact λ h, h₁ _ h}, rw [imp_not_comm],
  apply not_imp_not.mpr (λ con, _), exact id, apply con, apply h₃,
  apply h₁, exact h₂
end

example (n : ℕ) (m : ℕ) : nat.succ n < nat.succ n + 1  :=
begin
  {[smt] eblast_using  [nat.add_one], exact nat.lt_succ_self _}
end

example : ∀ (F1 F2 F3 : Prop), ((¬F1 ∧ F3) ∨ (F2 ∧ ¬F3)) → (F2 → F1) → (F2 → F3) →  ¬F2 :=
begin
  intros P Q R H₁ H₂ H₃ H₄,
  apply H₁.elim, -- `gptf {pfx := "apply"}`
  { assume h, simp * at * }, -- `gptf`
  cc -- `gptf`
end

example : ∀ (f : nat → Prop), f 2 → ∃ x, f x :=
begin
  exact λ f hf, ⟨_, hf⟩ -- by `gptf {pfx := "exact"}` :D
end

example {G : Type} [group G] (x y z : G) : (x * z) * (z⁻¹ * y) = x * y :=
begin
  simp [mul_assoc]  
end
universes u v

example {α : Type u} {β : α → Type v} [_inst_1 : decidable_eq α] {a : α} {l₁ l₂ : list (sigma β)} :
  (list.kerase a l₁).kunion (list.kerase a l₂) = list.kerase a (l₁.kunion l₂) :=
begin
  induction l₁ generalizing l₂, case list.nil { refl }, simp
end

end gptf
