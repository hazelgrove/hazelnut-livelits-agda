open import Nat
open import Prelude
open import List
open import core

module correspondence where
  mutual
    correspondence-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : dhexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Γ ⊢ e => τ
    correspondence-synth ESConst = SConst
    correspondence-synth (ESVar x₁) = SVar x₁
    correspondence-synth (ESLam apt ex) with correspondence-synth ex
    ... | ih = SLam apt ih
    correspondence-synth (ESAp x₁ x₂ x₃) = SAp (correspondence-synth x₁) x₂ (correspondence-ana x₃)
    correspondence-synth ESEHole = SEHole
    correspondence-synth (ESNEHole ex) = SNEHole (correspondence-synth ex)
    correspondence-synth (ESAsc x) = SAsc (correspondence-ana x)

    correspondence-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : dhexp} {Δ : hctx} →
                          Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                          Γ ⊢ e <= τ
    correspondence-ana (EALam apt ex) = ALam apt MAArr (correspondence-ana ex)
    correspondence-ana (EALamHole apt D) = ALam apt MAHole (correspondence-ana D)
    correspondence-ana (EASubsume x x₁ x₂ x₃) = ASubsume (correspondence-synth x₂) x₃
    correspondence-ana EAEHole = ASubsume SEHole TCHole1
    correspondence-ana (EANEHole x) = ASubsume (SNEHole (correspondence-synth x)) TCHole1
