open import Nat
open import Prelude
open import contexts
open import core

module canonical-value-forms where
  canonical-value-forms-b : ∀{Δ d} →
                            Δ , ∅ ⊢ d :: b →
                            d val →
                            d == c
  canonical-value-forms-b TAConst VConst = refl
  canonical-value-forms-b (TAVar x₁) ()
  canonical-value-forms-b (TAAp wt wt₁) ()
  canonical-value-forms-b (TAEHole x x₁) ()
  canonical-value-forms-b (TANEHole x wt x₁) ()
  canonical-value-forms-b (TACast wt x) ()
  canonical-value-forms-b (TAFailedCast wt x x₁ x₂) ()
  canonical-value-forms-b (TAFst wt) ()
  canonical-value-forms-b (TASnd wt) ()

  canonical-value-forms-arr : ∀{Δ d τ1 τ2} →
                              Δ , ∅ ⊢ d :: (τ1 ==> τ2) →
                              d val →
                              Σ[ x ∈ Nat ] Σ[ d' ∈ iexp ]
                                ((d == (·λ x [ τ1 ] d')) ×
                                 (Δ , ■ (x , τ1) ⊢ d' :: τ2))
  canonical-value-forms-arr (TAVar x₁) ()
  canonical-value-forms-arr (TALam _ wt) VLam = _ , _ , refl , wt
  canonical-value-forms-arr (TAAp wt wt₁) ()
  canonical-value-forms-arr (TAEHole x x₁) ()
  canonical-value-forms-arr (TANEHole x wt x₁) ()
  canonical-value-forms-arr (TACast wt x) ()
  canonical-value-forms-arr (TAFailedCast x x₁ x₂ x₃) ()
  canonical-value-forms-arr (TAFst wt) ()
  canonical-value-forms-arr (TASnd wt) ()

  canonical-value-forms-prod : ∀{Δ d τ1 τ2} →
                               Δ , ∅ ⊢ d :: (τ1 ⊗ τ2) →
                               d val →
                               Σ[ d1 ∈ iexp ] Σ[ d2 ∈ iexp ]
                                 ((d == ⟨ d1 , d2 ⟩ ) ×
                                  (Δ , ∅ ⊢ d1 :: τ1) ×
                                  (Δ , ∅ ⊢ d2 :: τ2))
  canonical-value-forms-prod (TAVar x₁) ()
  canonical-value-forms-prod (TAAp wt wt₁) ()
  canonical-value-forms-prod (TAEHole x x₁) ()
  canonical-value-forms-prod (TANEHole x wt x₁) ()
  canonical-value-forms-prod (TACast wt x) ()
  canonical-value-forms-prod (TAFailedCast wt x x₁ x₂) ()
  canonical-value-forms-prod (TAFst wt) ()
  canonical-value-forms-prod (TASnd wt) ()
  canonical-value-forms-prod (TAPair wt wt₁) (VPair dv dv₁) = _ , _ , refl , wt , wt₁

  -- this argues (somewhat informally, because you still have to inspect
  -- the types of the theorems above and manually verify this property)
  -- that we didn't miss any cases above; this intentionally will make this
  -- file fail to typecheck if we added more types, hopefully forcing us to
  -- remember to add canonical forms lemmas as appropriate
  canonical-value-forms-coverage1 : ∀{Δ d τ} →
                                   Δ , ∅ ⊢ d :: τ →
                                   d val →
                                   τ ≠ b →
                                   ((τ1 : typ) (τ2 : typ) → τ ≠ (τ1 ==> τ2)) →
                                   ((τ1 : typ) (τ2 : typ) → τ ≠ (τ1 ⊗ τ2)) →
                                   ⊥
  canonical-value-forms-coverage1 TAConst VConst = λ z _ _ → z refl
  canonical-value-forms-coverage1 (TAVar x₁) ()
  canonical-value-forms-coverage1 (TALam _ wt) VLam = λ _ z _ → z _ _ refl
  canonical-value-forms-coverage1 (TAAp wt wt₁) ()
  canonical-value-forms-coverage1 (TAEHole x x₁) ()
  canonical-value-forms-coverage1 (TANEHole x wt x₁) ()
  canonical-value-forms-coverage1 (TACast wt x) ()
  canonical-value-forms-coverage1 (TAFailedCast wt x x₁ x₂) ()
  canonical-value-forms-coverage1 (TAFst wt) ()
  canonical-value-forms-coverage1 (TASnd wt) ()
  canonical-value-forms-coverage1 (TAPair wt wt₁) (VPair dv dv₁) ne h = λ z → z _ _ refl

  canonical-value-forms-coverage2 : ∀{Δ d} →
                                   Δ , ∅ ⊢ d :: ⦇·⦈ →
                                   d val →
                                   ⊥
  canonical-value-forms-coverage2 (TAVar x₁) ()
  canonical-value-forms-coverage2 (TAAp wt wt₁) ()
  canonical-value-forms-coverage2 (TAEHole x x₁) ()
  canonical-value-forms-coverage2 (TANEHole x wt x₁) ()
  canonical-value-forms-coverage2 (TACast wt x) ()
  canonical-value-forms-coverage2 (TAFailedCast wt x x₁ x₂) ()
  canonical-value-forms-coverage2 (TAFst wt) ()
  canonical-value-forms-coverage2 (TASnd wt) ()
