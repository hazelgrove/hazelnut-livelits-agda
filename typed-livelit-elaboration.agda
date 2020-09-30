open import Prelude
open import core
open import contexts
open import weakening
open import livelits-checks

module typed-livelit-elaboration where
  mutual
    typed-livelit-elaboration-synth : ∀{Φ Γ p e τ} →
                                      Φ , Γ ⊢ p ~~> e ⇒ τ →
                                      Γ ⊢ e => τ
    typed-livelit-elaboration-synth SPEConst = SConst
    typed-livelit-elaboration-synth (SPEAsc x) = SAsc (typed-livelit-elaboration-ana x)
    typed-livelit-elaboration-synth (SPEVar x₁) = SVar x₁
    typed-livelit-elaboration-synth (SPELam x₁ D) = SLam x₁ (typed-livelit-elaboration-synth D)
    typed-livelit-elaboration-synth (SPEAp D1 x D2 x₂) = SAp x₂ (typed-livelit-elaboration-synth D1) x (typed-livelit-elaboration-ana D2)
    typed-livelit-elaboration-synth SPEHole = SEHole
    typed-livelit-elaboration-synth (SPNEHole x D) = SNEHole x (typed-livelit-elaboration-synth D)
    typed-livelit-elaboration-synth (SPELetPal _ _ D) = typed-livelit-elaboration-synth D
    typed-livelit-elaboration-synth (SPEApPal hd fr x x₁ x₂ x₃ x₄ x₅) = SAp (HDAsc hd) (SAsc (weaken-ana-closed fr x₅)) MAArr (typed-livelit-elaboration-ana x₄)
    typed-livelit-elaboration-synth (SPELetFPal _ _ D) = typed-livelit-elaboration-synth D
    typed-livelit-elaboration-synth {Φ} (SPEApFPal hd1 hd2 hd3 fr1 fr2 h h1 h2) =
      SAp (HDAp (HDAsc hd2) hd3) (SAp (HDAsc hd1) (SAsc (weaken-ana-closed fr1 (llctx-well-typed Φ h))) MAArr (weaken-ana-closed fr2 h2)) MAArr (typed-livelit-elaboration-ana h1)
    typed-livelit-elaboration-synth (SPEFst h x) = SFst (typed-livelit-elaboration-synth h) x
    typed-livelit-elaboration-synth (SPESnd h x) = SSnd (typed-livelit-elaboration-synth h) x
    typed-livelit-elaboration-synth (SPEPair h h₁ x) = SPair x (typed-livelit-elaboration-synth h) (typed-livelit-elaboration-synth h₁)

    typed-livelit-elaboration-ana : ∀{Φ Γ p e τ} →
                                  Φ , Γ ⊢ p ~~> e ⇐ τ →
                                  Γ ⊢ e <= τ
    typed-livelit-elaboration-ana (APELam x₁ x₂ D) = ALam x₁ x₂ (typed-livelit-elaboration-ana D)
    typed-livelit-elaboration-ana (APESubsume h ch) = ASubsume (typed-livelit-elaboration-synth h) ch
    typed-livelit-elaboration-ana (APELetPal pcH x D) = typed-livelit-elaboration-ana D
    typed-livelit-elaboration-ana (APELetFPal pcH x D) = typed-livelit-elaboration-ana D
