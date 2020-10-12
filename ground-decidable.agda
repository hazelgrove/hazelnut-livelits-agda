open import Prelude
open import core

module ground-decidable where
  -- every type is either ground or not
  ground-decidable : (τ : typ) → (τ ground) + ((τ ground) → ⊥)
  ground-decidable b = Inl GBase
  ground-decidable ⦇·⦈ = Inr (λ ())
  ground-decidable (b ==> b) = Inr (λ ())
  ground-decidable (b ==> ⦇·⦈) = Inr (λ ())
  ground-decidable (b ==> τ' ==> τ'') = Inr (λ ())
  ground-decidable (b ==> τ₁ ⊗ τ₂) = Inr (λ ())
  ground-decidable (⦇·⦈ ==> b) = Inr (λ ())
  ground-decidable (⦇·⦈ ==> ⦇·⦈) = Inl GHole
  ground-decidable (⦇·⦈ ==> τ' ==> τ'') = Inr (λ ())
  ground-decidable ((τ ==> τ₁) ==> b) = Inr (λ ())
  ground-decidable ((τ ==> τ₁) ==> ⦇·⦈) = Inr (λ ())
  ground-decidable ((τ ==> τ₁) ==> τ' ==> τ'') = Inr (λ ())
  ground-decidable ((τ ⊗ τ₂) ==> τ₁) = Inr (λ ())
  ground-decidable (τ ⊗ b) = Inr (λ ())
  ground-decidable (b ⊗ ⦇·⦈) = Inr (λ ())
  ground-decidable (⦇·⦈ ⊗ ⦇·⦈) = Inl GProd
  ground-decidable (⦇·⦈ ==> τ₁ ⊗ τ₂) = Inr (λ ())
  ground-decidable ((τ ⊗ τ₁) ⊗ ⦇·⦈) = Inr (λ ())
  ground-decidable ((τ ==> τ₁) ⊗ ⦇·⦈) = Inr (λ ())
  ground-decidable ((τ ==> τ₂) ==> τ₁ ⊗ τ₃) = Inr (λ ())
  ground-decidable (τ ⊗ τ₁ ==> τ₂) = Inr (λ ())
  ground-decidable (τ ⊗ τ₁ ⊗ τ₂) = Inr (λ ())
