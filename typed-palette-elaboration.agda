open import Prelude
open import core
open import contexts
open import weakening
open import palettes-checks

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
    typed-palette-elaboration-synth (SPELetPal _ _ D) = typed-palette-elaboration-synth D
    typed-palette-elaboration-synth (SPEApPal hd fr x x₁ x₂ x₃ x₄ x₅) = SAp (HDAsc hd) (SAsc (weaken-ana-closed fr x₅)) MAArr (typed-palette-elaboration-ana x₄)
    typed-palette-elaboration-synth (SPELetFPal _ _ D) = typed-palette-elaboration-synth D
    typed-palette-elaboration-synth {Φ} (SPEApFPal hd1 hd2 hd3 fr1 fr2 h h1 h2) =
      SAp (HDAp (HDAsc hd2) hd3) (SAp (HDAsc hd1) (SAsc (weaken-ana-closed fr1 (palctx-well-typed Φ h))) MAArr (weaken-ana-closed fr2 h2)) MAArr (typed-palette-elaboration-ana h1)
    typed-palette-elaboration-synth (SPEFst h x) = SFst (typed-palette-elaboration-synth h) x
    typed-palette-elaboration-synth (SPESnd h x) = SSnd (typed-palette-elaboration-synth h) x
    typed-palette-elaboration-synth (SPEPair h h₁ x) = SPair x (typed-palette-elaboration-synth h) (typed-palette-elaboration-synth h₁)

    typed-palette-elaboration-ana : ∀{Φ Γ p e τ} →
                                  Φ , Γ ⊢ p ~~> e ⇐ τ →
                                  Γ ⊢ e <= τ
    typed-palette-elaboration-ana (APELam x₁ x₂ D) = ALam x₁ x₂ (typed-palette-elaboration-ana D)
    typed-palette-elaboration-ana (APESubsume h ch) = ASubsume (typed-palette-elaboration-synth h) ch
    typed-palette-elaboration-ana (APELetPal pcH x D) = typed-palette-elaboration-ana D
    typed-palette-elaboration-ana (APELetFPal pcH x D) = typed-palette-elaboration-ana D
