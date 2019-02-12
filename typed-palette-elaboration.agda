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
    typed-palette-elaboration-synth (SPEAp D1 x D2 x₂) = SAp x₂ (typed-palette-elaboration-synth D1) x (typed-palette-elaboration-ana D2)
    typed-palette-elaboration-synth SPEHole = SEHole
    typed-palette-elaboration-synth (SPNEHole x D) = SNEHole x (typed-palette-elaboration-synth D)
    typed-palette-elaboration-synth (SPELetPal x D) = typed-palette-elaboration-synth D
    typed-palette-elaboration-synth (SPEApPal hd x x₁ x₂ x₃ x₄ x₅) = SAp (HDAsc hd) (SAsc {!x₅!}) MAArr (typed-palette-elaboration-ana x₄)

    typed-palette-elaboration-ana : ∀{Φ Γ p e τ} →
                                  Φ , Γ ⊢ p ~~> e ⇐ τ →
                                  Γ ⊢ e <= τ
    typed-palette-elaboration-ana (APELam x₁ x₂ D) = ALam x₁ x₂ (typed-palette-elaboration-ana D)
    typed-palette-elaboration-ana (APESubsume x x₁) = ASubsume (typed-palette-elaboration-synth x) x₁
    typed-palette-elaboration-ana (APELetPal x D) = typed-palette-elaboration-ana D
