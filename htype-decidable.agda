open import Nat
open import Prelude
open import core
open import contexts

module htype-decidable where
  lemma-arr-l : ∀{t1 t2 t4} → t1 ==> t2 == t1 ==> t4 → t2 == t4
  lemma-arr-l refl = refl

  lemma-arr-r : ∀{t1 t2 t3} → t1 ==> t2 == t3 ==> t2 → t1 == t3
  lemma-arr-r refl = refl

  lemma-arr-b : ∀{t1 t2 t3 t4} → t1 ==> t2 == t3 ==> t4 → t1 == t3
  lemma-arr-b refl = refl

  lemma-prod-l : ∀{t1 t2 t4} → t1 ⊗ t2 == t1 ⊗ t4 → t2 == t4
  lemma-prod-l refl = refl

  lemma-prod-r : ∀{t1 t2 t3} → t1 ⊗ t2 == t3 ⊗ t2 → t1 == t3
  lemma-prod-r refl = refl

  lemma-prod-b : ∀{t1 t2 t3 t4} → t1 ⊗ t2 == t3 ⊗ t4 → t1 == t3
  lemma-prod-b refl = refl

  htype-dec : dec typ
  htype-dec b b = Inl refl
  htype-dec b ⦇·⦈ = Inr (λ ())
  htype-dec b (t2 ==> t3) = Inr (λ ())
  htype-dec ⦇·⦈ b = Inr (λ ())
  htype-dec ⦇·⦈ ⦇·⦈ = Inl refl
  htype-dec ⦇·⦈ (t2 ==> t3) = Inr (λ ())
  htype-dec (t1 ==> t2) b = Inr (λ ())
  htype-dec (t1 ==> t2) ⦇·⦈ = Inr (λ ())
  htype-dec (t1 ==> t2) (t3 ==> t4) with htype-dec t1 t3 | htype-dec t2 t4
  htype-dec (t1 ==> t2) (.t1 ==> .t2) | Inl refl | Inl refl = Inl refl
  htype-dec (t1 ==> t2) (.t1 ==> t4)  | Inl refl | Inr x₁   = Inr (λ x → x₁ (lemma-arr-l x))
  htype-dec (t1 ==> t2) (t3 ==> .t2)  | Inr x    | Inl refl = Inr (λ x₁ → x (lemma-arr-r x₁))
  htype-dec (t1 ==> t2) (t3 ==> t4)   | Inr x    | Inr x₁   = Inr (λ x₂ → x (lemma-arr-b x₂))
  htype-dec b (t2 ⊗ t3) = Inr (λ ())
  htype-dec ⦇·⦈ (t2 ⊗ t3) = Inr (λ ())
  htype-dec (t1 ==> t2) (t3 ⊗ t4) = Inr (λ ())
  htype-dec (t1 ⊗ t2) b = Inr (λ ())
  htype-dec (t1 ⊗ t2) ⦇·⦈ = Inr (λ ())
  htype-dec (t1 ⊗ t2) (t3 ==> t4) = Inr (λ ())
  htype-dec (t1 ⊗ t2) (t3 ⊗ t4) with htype-dec t1 t3 | htype-dec t2 t4
  htype-dec (t1 ⊗ t2) (.t1 ⊗ .t2) | Inl refl | Inl refl = Inl refl
  htype-dec (t1 ⊗ t2) (.t1 ⊗ t4)  | Inl refl | Inr x₁   = Inr (λ x → x₁ (lemma-prod-l x))
  htype-dec (t1 ⊗ t2) (t3 ⊗ .t2)  | Inr x    | Inl refl = Inr (λ x' → x (lemma-prod-r x'))
  htype-dec (t1 ⊗ t2) (t3 ⊗ t4)   | Inr x    | Inr x₁   = Inr (λ x' → x (lemma-prod-b x'))

  -- if an arrow is disequal, it disagrees in the first or second argument
  ne-factor : ∀{τ1 τ2 τ3 τ4} → (τ1 ==> τ2) ≠ (τ3 ==> τ4) → (τ1 ≠ τ3) + (τ2 ≠ τ4)
  ne-factor {τ1} {τ2} {τ3} {τ4} ne with htype-dec τ1 τ3 | htype-dec τ2 τ4
  ne-factor ne | Inl refl | Inl refl = Inl (λ x → ne refl)
  ne-factor ne | Inl x | Inr x₁ = Inr x₁
  ne-factor ne | Inr x | Inl x₁ = Inl x
  ne-factor ne | Inr x | Inr x₁ = Inl x
