open import core
open import contexts

module typed-palette-elaboration where
  typed-palette-elaboration-synth : ∀{Φ Γ p d τ} →
                              Φ , Γ ⊢ p ~~> d ⇒ τ →
                              Γ ⊢ d => τ
  typed-palette-elaboration-synth SPEConst = SConst
  typed-palette-elaboration-synth (SPEAsc exp) = SAsc (ASubsume (typed-palette-elaboration-synth exp) TCRefl)
  typed-palette-elaboration-synth (SPEVar x₁) = SVar x₁
  typed-palette-elaboration-synth (SPELam apt exp) = SLam apt (typed-palette-elaboration-synth exp)

  typed-palette-elaboration-ana : ∀{Φ Γ p d τ} →
                              Φ , Γ ⊢ p ~~> d ⇐ τ →
                              Γ ⊢ d <= τ
  typed-palette-elaboration-ana = {!!}
