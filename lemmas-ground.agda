open import Prelude
open import core

module lemmas-ground where
  -- not ground types aren't hole to hole
  ground-arr-not-hole : ∀{τ} →
                      (τ ground → ⊥) →
                      (τ ≠ (⦇·⦈ ==> ⦇·⦈))
  ground-arr-not-hole notg refl = notg GHole

  ground-prod-not-hole : ∀{τ} →
                     (τ ground → ⊥) →
                     (τ ≠ (⦇·⦈ ⊗ ⦇·⦈))
  ground-prod-not-hole notg refl = notg GProd

  -- not ground types either have to be hole or an arrow or a prod
  notground : ∀{τ} →
              (τ ground → ⊥) →
              (τ == ⦇·⦈) +
                (Σ[ τ1 ∈ typ ] Σ[ τ2 ∈ typ ] (τ == (τ1 ==> τ2))) +
                (Σ[ τ1 ∈ typ ] Σ[ τ2 ∈ typ ] (τ == (τ1 ⊗ τ2)))
  notground {b} gnd = abort (gnd GBase)
  notground {⦇·⦈} gnd = Inl refl
  notground {τ ==> τ₁} gnd = Inr (Inl (τ , τ₁ , refl))
  notground {τ ⊗ τ₁} gnd = Inr (Inr (τ , τ₁ , refl))

  ground-arr-lem :
                   (τ : typ) →
                   ((τ ground) → ⊥) →
                   (τ ≠  ⦇·⦈) →
                   Σ[ τ1 ∈ typ ] Σ[ τ2 ∈ typ ]
                     (((τ == (τ1 ==> τ2)) × ((τ1 ==> τ2) ≠ (⦇·⦈ ==> ⦇·⦈))) +
                      ((τ == (τ1 ⊗ τ2))  × ((τ1 ⊗ τ2)   ≠ (⦇·⦈ ⊗ ⦇·⦈))))
  ground-arr-lem b ng nh = abort (ng GBase)
  ground-arr-lem ⦇·⦈ ng nh = abort (nh refl)
  ground-arr-lem (τ1 ==> τ2) ng nh = τ1 , τ2 , Inl (refl , λ x → ng (lem' x))
    where
      lem' : ∀{τ1 τ2} → τ1 ==> τ2 == ⦇·⦈ ==> ⦇·⦈ → (τ1 ==> τ2) ground
      lem' refl = GHole
  ground-arr-lem (τ1 ⊗ τ2) ng nh = τ1 , τ2 , Inr (refl , (λ x → ng (lem' x)))
    where
      lem' : ∀{τ1 τ2} → τ1 ⊗ τ2 == ⦇·⦈ ⊗ ⦇·⦈ → (τ1 ⊗ τ2) ground
      lem' refl = GProd
