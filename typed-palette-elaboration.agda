open import core
open import contexts

module typed-palette-elaboration where
  mutual
    typed-palette-elaboration-synth : ∀{Φ Γ p e τ} →
                                      Φ , Γ ⊢ p ~~> e ⇒ τ →
                                      Γ ⊢ e => τ
    typed-palette-elaboration-synth SPEConst = SConst
    typed-palette-elaboration-synth (SPEAsc x) = SAsc (typed-palette-elaboration-ana x)
    typed-palette-elaboration-synth (SPEVar x₁) = SVar x₁
    typed-palette-elaboration-synth (SPELam x₁ D) = SLam x₁ (typed-palette-elaboration-synth D)
    typed-palette-elaboration-synth (SPEAp D x x₁ x₂) = {!!}
    typed-palette-elaboration-synth SPEHole = SEHole
    typed-palette-elaboration-synth (SPNEHole x D) = SNEHole x (typed-palette-elaboration-synth D)
    typed-palette-elaboration-synth (SPELetPal x D) = typed-palette-elaboration-synth D
    typed-palette-elaboration-synth (SPEApPal x x₁ x₂ x₃ x₄ x₅) = {!!}

    typed-palette-elaboration-ana : ∀{Φ Γ p e τ} →
                                  Φ , Γ ⊢ p ~~> e ⇐ τ →
                                  Γ ⊢ e <= τ
    typed-palette-elaboration-ana (APELam x₁ x₂ D) = ALam x₁ x₂ (typed-palette-elaboration-ana D)
    typed-palette-elaboration-ana (APESubsume x x₁) = {!!}
    typed-palette-elaboration-ana (APELetPal x D) = typed-palette-elaboration-ana D
