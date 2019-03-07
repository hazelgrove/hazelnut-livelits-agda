open import core
open import contexts
open import weakening

module typed-palette-elaboration where
  mutual
    typed-palette-elaboration-synth : ∀{Φ Γ p e τ} →
                                      Φ , Γ ⊢ p ~~> e ⇒ τ →
                                      Γ ⊢ e => τ
    typed-palette-elaboration-synth (SPEConst pcH) = SConst
    typed-palette-elaboration-synth (SPEAsc pcH x) = SAsc (typed-palette-elaboration-ana x)
    typed-palette-elaboration-synth (SPEVar pcH x₁) = SVar x₁
    typed-palette-elaboration-synth (SPELam pcH x₁ D) = SLam x₁ (typed-palette-elaboration-synth D)
    typed-palette-elaboration-synth (SPEAp pcH D1 x D2 x₂) = SAp x₂ (typed-palette-elaboration-synth D1) x (typed-palette-elaboration-ana D2)
    typed-palette-elaboration-synth (SPEHole pcH) = SEHole
    typed-palette-elaboration-synth (SPNEHole pcH x D) = SNEHole x (typed-palette-elaboration-synth D)
    typed-palette-elaboration-synth (SPELetPal pcH x D) = typed-palette-elaboration-synth D
    typed-palette-elaboration-synth (SPEApPal pcH hd fr x x₁ x₂ x₃ x₄ x₅) = SAp (HDAsc hd) (SAsc (weaken-ana-closed fr x₅)) MAArr (typed-palette-elaboration-ana x₄)
    typed-palette-elaboration-synth (SPELetFPal pcH x D) = typed-palette-elaboration-synth D
    typed-palette-elaboration-synth (SPEApFPal pcH hd1 hd2 hd3 fr1 fr2 h h1 h2) =
      SAp (HDAp (HDAsc hd2) hd3) (SAp (HDAsc hd1) (SAsc (weaken-ana-closed fr1 (palctx-well-typed pcH h))) MAArr (weaken-ana-closed fr2 h2)) MAArr (typed-palette-elaboration-ana h1)

    typed-palette-elaboration-ana : ∀{Φ Γ p e τ} →
                                  Φ , Γ ⊢ p ~~> e ⇐ τ →
                                  Γ ⊢ e <= τ
    typed-palette-elaboration-ana (APELam pcH x₁ x₂ D) = ALam x₁ x₂ (typed-palette-elaboration-ana D)
    typed-palette-elaboration-ana (APESubsume pcH x x₁) = ASubsume (typed-palette-elaboration-synth x) x₁
    typed-palette-elaboration-ana (APELetPal pcH x D) = typed-palette-elaboration-ana D
    typed-palette-elaboration-ana (APELetFPal pcH x D) = typed-palette-elaboration-ana D
