open import Prelude
open import core
open import contexts
open import weakening

module typed-expansion where
  mutual
    typed-expansion-synth : ∀{Φ Γ p e τ} →
                                      Φ , Γ ⊢ p ~~> e ⇒ τ →
                                      Γ ⊢ e => τ
    typed-expansion-synth SPEConst = SConst
    typed-expansion-synth (SPEAsc x) = SAsc (typed-expansion-ana x)
    typed-expansion-synth (SPEVar x₁) = SVar x₁
    typed-expansion-synth (SPELam x₁ D) = SLam x₁ (typed-expansion-synth D)
    typed-expansion-synth (SPEAp D1 x D2 x₂) = SAp x₂ (typed-expansion-synth D1) x (typed-expansion-ana D2)
    typed-expansion-synth SPEHole = SEHole
    typed-expansion-synth (SPNEHole x D) = SNEHole x (typed-expansion-synth D)
    typed-expansion-synth (SPEApLivelit hd fr x x₁ x₂ x₃ x₄ x₅) = SAp (HDAsc hd) (SAsc (weaken-ana-closed fr x₅)) MAArr (typed-expansion-ana x₄)
    typed-expansion-synth (SPEFst h x) = SFst (typed-expansion-synth h) x
    typed-expansion-synth (SPESnd h x) = SSnd (typed-expansion-synth h) x
    typed-expansion-synth (SPEPair h h₁ x) = SPair x (typed-expansion-synth h) (typed-expansion-synth h₁)

    typed-expansion-ana : ∀{Φ Γ p e τ} →
                                  Φ , Γ ⊢ p ~~> e ⇐ τ →
                                  Γ ⊢ e <= τ
    typed-expansion-ana (APELam x₁ x₂ D) = ALam x₁ x₂ (typed-expansion-ana D)
    typed-expansion-ana (APESubsume h ch) = ASubsume (typed-expansion-synth h) ch
