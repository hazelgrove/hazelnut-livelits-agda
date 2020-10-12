open import Nat
open import Prelude
open import core
open import contexts

module typ-dec where
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

  -- types are decidable
  typ-dec : dec typ
  typ-dec b b = Inl refl
  typ-dec b ⦇·⦈ = Inr (λ ())
  typ-dec b (t2 ==> t3) = Inr (λ ())
  typ-dec ⦇·⦈ b = Inr (λ ())
  typ-dec ⦇·⦈ ⦇·⦈ = Inl refl
  typ-dec ⦇·⦈ (t2 ==> t3) = Inr (λ ())
  typ-dec (t1 ==> t2) b = Inr (λ ())
  typ-dec (t1 ==> t2) ⦇·⦈ = Inr (λ ())
  typ-dec (t1 ==> t2) (t3 ==> t4) with typ-dec t1 t3 | typ-dec t2 t4
  typ-dec (t1 ==> t2) (.t1 ==> .t2) | Inl refl | Inl refl = Inl refl
  typ-dec (t1 ==> t2) (.t1 ==> t4)  | Inl refl | Inr x₁   = Inr (λ x → x₁ (lemma-arr-l x))
  typ-dec (t1 ==> t2) (t3 ==> .t2)  | Inr x    | Inl refl = Inr (λ x₁ → x (lemma-arr-r x₁))
  typ-dec (t1 ==> t2) (t3 ==> t4)   | Inr x    | Inr x₁   = Inr (λ x₂ → x (lemma-arr-b x₂))
  typ-dec b (t2 ⊗ t3) = Inr (λ ())
  typ-dec ⦇·⦈ (t2 ⊗ t3) = Inr (λ ())
  typ-dec (t1 ==> t2) (t3 ⊗ t4) = Inr (λ ())
  typ-dec (t1 ⊗ t2) b = Inr (λ ())
  typ-dec (t1 ⊗ t2) ⦇·⦈ = Inr (λ ())
  typ-dec (t1 ⊗ t2) (t3 ==> t4) = Inr (λ ())
  typ-dec (t1 ⊗ t2) (t3 ⊗ t4) with typ-dec t1 t3 | typ-dec t2 t4
  typ-dec (t1 ⊗ t2) (.t1 ⊗ .t2) | Inl refl | Inl refl = Inl refl
  typ-dec (t1 ⊗ t2) (.t1 ⊗ t4)  | Inl refl | Inr x₁   = Inr (λ x → x₁ (lemma-prod-l x))
  typ-dec (t1 ⊗ t2) (t3 ⊗ .t2)  | Inr x    | Inl refl = Inr (λ x' → x (lemma-prod-r x'))
  typ-dec (t1 ⊗ t2) (t3 ⊗ t4)   | Inr x    | Inr x₁   = Inr (λ x' → x (lemma-prod-b x'))

  -- if an arrow is disequal, it disagrees in the first or second argument
  ne-factor : ∀{τ1 τ2 τ3 τ4} → (τ1 ==> τ2) ≠ (τ3 ==> τ4) → (τ1 ≠ τ3) + (τ2 ≠ τ4)
  ne-factor {τ1} {τ2} {τ3} {τ4} ne with typ-dec τ1 τ3 | typ-dec τ2 τ4
  ne-factor ne | Inl refl | Inl refl = Inl (λ x → ne refl)
  ne-factor ne | Inl x | Inr x₁ = Inr x₁
  ne-factor ne | Inr x | Inl x₁ = Inl x
  ne-factor ne | Inr x | Inr x₁ = Inl x
