open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-matching

module expansion-unicity where

  mutual
    expansion-unicity-synth : ∀{Φ Γ P e1 τ1 e2 τ2} →
      Φ , Γ ⊢ P ~~> e1 ⇒ τ1 →
      Φ , Γ ⊢ P ~~> e2 ⇒ τ2 →
      (e1 == e2) × (τ1 == τ2)
    expansion-unicity-synth SPEConst SPEConst = refl , refl
    expansion-unicity-synth (SPEAsc x) (SPEAsc x₁) with expansion-unicity-ana x x₁
    ... | refl , refl = refl , refl
    expansion-unicity-synth {Γ = Γ} (SPEVar x₁) (SPEVar x₂) with ctxunicity {Γ = Γ} x₁ x₂
    ... | refl = refl , refl
    expansion-unicity-synth (SPELam x₁ D1) (SPELam x₂ D2) with expansion-unicity-synth D1 D2
    ... | refl , refl = refl , refl
    expansion-unicity-synth (SPEAp D1 x x₁ x₂) (SPEAp D2 x₃ x₄ x₅) with expansion-unicity-synth D1 D2 | expansion-unicity-ana x₁ x₄
    ... | refl , refl | refl , refl with ▸arr-unicity x x₃
    ... | refl = refl , refl
    expansion-unicity-synth SPEHole SPEHole = refl , refl
    expansion-unicity-synth (SPNEHole x D1) (SPNEHole x₁ D2) with expansion-unicity-synth D1 D2
    ... | refl , refl = refl , refl
    expansion-unicity-synth (SPEFst D1 x) (SPEFst D2 x₁) with expansion-unicity-synth D1 D2
    ... | refl , refl with ▸prod-unicity x x₁
    ... | refl = refl , refl
    expansion-unicity-synth (SPESnd D1 x) (SPESnd D2 x₁) with expansion-unicity-synth D1 D2
    ... | refl , refl with ▸prod-unicity x x₁
    ... | refl = refl , refl
    expansion-unicity-synth (SPEPair D1 D2 x) (SPEPair D3 D4 x₁) with expansion-unicity-synth D1 D3 | expansion-unicity-synth D2 D4
    ... | refl , refl | refl , refl = refl , refl
    expansion-unicity-synth (SPELetPal #h x D1) (SPELetPal #h₁ x₁ D2) = {!!}
    expansion-unicity-synth (SPEApPal x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (SPEApPal x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) with expansion-unicity-ana x₆ x₁₄
    ... | refl , refl with someinj (! x₁₀ · x₂)
    ... | refl =  {!!} , refl --  i think we might need something about
                              --  denc that the postulate junk doesn't give
                              --  us right here. you need to know that the
                              --  two eexpandeds are the same.
    expansion-unicity-synth (SPELetFPal #h eh D1) (SPELetFPal #h₁ eh₁ D2) = {!!}
    expansion-unicity-synth (SPEApFPal x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (SPEApFPal x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) = {!!}

    expansion-unicity-ana : ∀{Φ Γ P e1 τ1 e2 τ2} →
      Φ , Γ ⊢ P ~~> e1 ⇐ τ1 →
      Φ , Γ ⊢ P ~~> e2 ⇐ τ2 →
      (e1 == e2) × (τ1 == τ2)
    expansion-unicity-ana D1 (APESubsume x₃ x₄) = {!!}
    expansion-unicity-ana (APESubsume x₃ x₄) D2 = {!!}
    expansion-unicity-ana (APELam x₁ x₂ D1) (APELam x₃ x₄ D2) = {!!}
    expansion-unicity-ana (APELetPal #h x D1) (APELetPal #h₁ x₁ D2) = {!!}
    expansion-unicity-ana (APELetFPal #h eh D1) (APELetFPal #h₁ eh₁ D2) = {!!}
