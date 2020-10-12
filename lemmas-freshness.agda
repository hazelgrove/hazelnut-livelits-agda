open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness

module lemmas-freshness where
  -- if x is fresh in an eexp, it's fresh in its expansion
  mutual
    fresh-elab-synth1 : ∀{x e τ d Γ Δ} →
                         x # Γ →
                         freshe x e →
                         Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                         fresh x d
    fresh-elab-synth1 _ FRHConst ESConst = FConst
    fresh-elab-synth1 apt (FRHAsc frsh) (ESAsc x₁) = FCast (fresh-elab-ana1 apt frsh x₁)
    fresh-elab-synth1 _ (FRHVar x₂) (ESVar x₃) = FVar x₂
    fresh-elab-synth1 {Γ = Γ} apt (FRHLam2 x₂ frsh) (ESLam x₃ exp) = FLam x₂ (fresh-elab-synth1 (apart-extend1 Γ x₂ apt) frsh exp)
    fresh-elab-synth1 apt FRHEHole ESEHole = FHole (EFId apt)
    fresh-elab-synth1 apt (FRHNEHole frsh) (ESNEHole x₁ exp) = FNEHole (EFId apt) (fresh-elab-synth1 apt frsh exp)
    fresh-elab-synth1 apt (FRHAp frsh frsh₁) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) =
                               FAp (FCast (fresh-elab-ana1 apt frsh x₅))
                                   (FCast (fresh-elab-ana1 apt frsh₁ x₆))
    fresh-elab-synth1 apt (FRHLam1 x₁ frsh) ()
    fresh-elab-synth1 apt (FRHFst frsh) (ESFst s m esana) = FFst (FCast (fresh-elab-ana1 apt frsh esana))
    fresh-elab-synth1 apt (FRHSnd frsh) (ESSnd s m esana) = FSnd (FCast (fresh-elab-ana1 apt frsh esana))
    fresh-elab-synth1 apt (FRHPair frsh frsh₁) (ESPair x₁ x₂ exp exp₁) = FPair (fresh-elab-synth1 apt frsh exp)
                                                                           (fresh-elab-synth1 apt frsh₁ exp₁)

    fresh-elab-ana1 : ∀{ x e τ d τ' Γ Δ} →
                      x # Γ →
                      freshe x e →
                      Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      fresh x d
    fresh-elab-ana1 {Γ = Γ}  apt (FRHLam1 x₁ frsh) (EALam x₂ x₃ exp) = FLam x₁ (fresh-elab-ana1 (apart-extend1 Γ x₁ apt) frsh exp )
    fresh-elab-ana1 apt frsh (EASubsume x₁ x₂ x₃ x₄) = fresh-elab-synth1 apt frsh x₃
    fresh-elab-ana1 apt FRHEHole EAEHole = FHole (EFId apt)
    fresh-elab-ana1 apt (FRHNEHole frsh) (EANEHole x₁ x₂) = FNEHole (EFId apt) (fresh-elab-synth1 apt frsh x₂)

  -- if x is fresh in the expansion of an eexp, it's fresh in that eexp
  mutual
    fresh-elab-synth2 : ∀{x e τ d Γ Δ} →
                         fresh x d →
                         Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                         freshe x e
    fresh-elab-synth2 FConst ESConst = FRHConst
    fresh-elab-synth2 (FVar x₂) (ESVar x₃) = FRHVar x₂
    fresh-elab-synth2 (FLam x₂ frsh) (ESLam x₃ exp) = FRHLam2 x₂ (fresh-elab-synth2 frsh exp)
    fresh-elab-synth2 (FHole x₁) ESEHole = FRHEHole
    fresh-elab-synth2 (FNEHole x₁ frsh) (ESNEHole x₂ exp) = FRHNEHole (fresh-elab-synth2 frsh exp)
    fresh-elab-synth2 (FAp (FCast frsh) (FCast frsh₁)) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) =
                        FRHAp (fresh-elab-ana2 frsh x₅)
                              (fresh-elab-ana2 frsh₁ x₆)
    fresh-elab-synth2 (FCast frsh) (ESAsc x₁) = FRHAsc (fresh-elab-ana2 frsh x₁)
    fresh-elab-synth2 (FFailedCast frsh) ()
    fresh-elab-synth2 (FFst (FCast frsh)) (ESFst s m esana) = FRHFst (fresh-elab-ana2 frsh esana)
    fresh-elab-synth2 (FSnd (FCast frsh)) (ESSnd s m esana) = FRHSnd (fresh-elab-ana2 frsh esana)
    fresh-elab-synth2 (FPair frsh frsh₁) (ESPair x₁ x₂ exp exp₁) = FRHPair (fresh-elab-synth2 frsh exp) (fresh-elab-synth2 frsh₁ exp₁)

    fresh-elab-ana2 : ∀{ x e τ d τ' Γ Δ} →
                      fresh x d →
                      Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      freshe x e
    fresh-elab-ana2 (FLam x₁ frsh) (EALam x₂ x₃ exp) = FRHLam1 x₁ (fresh-elab-ana2 frsh exp)
    fresh-elab-ana2 frsh (EASubsume x₁ x₂ x₃ x₄) = fresh-elab-synth2 frsh x₃
    fresh-elab-ana2 (FHole x₁) EAEHole = FRHEHole
    fresh-elab-ana2 (FNEHole x₁ frsh) (EANEHole x₂ x₃) = FRHNEHole (fresh-elab-synth2 frsh x₃)
