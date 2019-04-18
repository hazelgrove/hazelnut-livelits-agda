open import Nat
open import Prelude
open import core

module expansion-unicity where

  expansion-unicity-synth : ∀{Φ Γ P e1 τ1 e2 τ2} →
    Φ , Γ ⊢ P ~~> e1 ⇒ τ1 →
    Φ , Γ ⊢ P ~~> e2 ⇒ τ2 →
    (e1 == e2) × (τ1 == τ2)
  expansion-unicity-synth = {!!}

  expansion-unicity-ana : ∀{Φ Γ P e1 τ1 e2 τ2} →
    Φ , Γ ⊢ P ~~> e1 ⇐ τ1 →
    Φ , Γ ⊢ P ~~> e2 ⇐ τ2 →
    (e1 == e2) × (τ1 == τ2)
  expansion-unicity-ana = {!!}
