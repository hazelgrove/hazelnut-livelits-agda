open import Nat
open import Prelude
open import core
open import contexts

open import lemmas-consistency
open import type-assignment-unicity
open import binders-disjoint-checks

open import lemmas-subst-ta

module preservation where
  -- if d and d' both result from filling the hole in ε with terms of the
  -- same type, they too have the same type.
  wt-different-fill : ∀{ Δ Γ d ε d1 d2 d' τ τ1 } →
            d == ε ⟦ d1 ⟧ →
            Δ , Γ ⊢ d :: τ →
            Δ , Γ ⊢ d1 :: τ1 →
            Δ , Γ ⊢ d2 :: τ1 →
            d' == ε ⟦ d2 ⟧ →
            Δ , Γ ⊢ d' :: τ
  wt-different-fill FHOuter D1 D2 D3 FHOuter
    with type-assignment-unicity D1 D2
  ... | refl = D3
  wt-different-fill (FHAp1 eps) (TAAp D1 D2) D3 D4 (FHAp1 D5) = TAAp (wt-different-fill eps D1 D3 D4 D5) D2
  wt-different-fill (FHAp2 eps) (TAAp D1 D2) D3 D4 (FHAp2 D5) = TAAp D1 (wt-different-fill eps D2 D3 D4 D5)
  wt-different-fill (FHNEHole eps) (TANEHole x D1 x₁) D2 D3 (FHNEHole D4) = TANEHole x (wt-different-fill eps D1 D2 D3 D4) x₁
  wt-different-fill (FHCast eps) (TACast D1 x) D2 D3 (FHCast D4) = TACast (wt-different-fill eps D1 D2 D3 D4) x
  wt-different-fill (FHFailedCast x) (TAFailedCast y x₁ x₂ x₃) D3 D4 (FHFailedCast eps) = TAFailedCast (wt-different-fill x y D3 D4 eps) x₁ x₂ x₃
  wt-different-fill (FHFst eps1) (TAFst ta) D3 D4 (FHFst eps2) = TAFst (wt-different-fill eps1 ta D3 D4 eps2)
  wt-different-fill (FHSnd eps1) (TASnd ta) D3 D4 (FHSnd eps2) = TASnd (wt-different-fill eps1 ta D3 D4 eps2)
  wt-different-fill (FHPair1 eps1) (TAPair ta ta₁) D3 D4 (FHPair1 eps2) = TAPair (wt-different-fill eps1 ta D3 D4 eps2) ta₁
  wt-different-fill (FHPair2 eps1) (TAPair ta ta₁) D3 D4 (FHPair2 eps2) = TAPair ta (wt-different-fill eps1 ta₁ D3 D4 eps2)

  -- if a well typed term results from filling the hole in ε, then the term
  -- that filled the hole is also well typed
  wt-filling : ∀{ ε Δ Γ d τ d' } →
             Δ , Γ ⊢ d :: τ →
             d == ε ⟦ d' ⟧ →
             Σ[ τ' ∈ typ ] (Δ , Γ ⊢ d' :: τ')
  wt-filling TAConst FHOuter = _ , TAConst
  wt-filling (TAVar x₁) FHOuter = _ , TAVar x₁
  wt-filling (TALam f ta) FHOuter = _ , TALam f ta

  wt-filling (TAAp ta ta₁) FHOuter = _ , TAAp ta ta₁
  wt-filling (TAAp ta ta₁) (FHAp1 eps) = wt-filling ta eps
  wt-filling (TAAp ta ta₁) (FHAp2 eps) = wt-filling ta₁ eps

  wt-filling (TAEHole x x₁) FHOuter = _ , TAEHole x x₁
  wt-filling (TANEHole x ta x₁) FHOuter = _ , TANEHole x ta x₁
  wt-filling (TANEHole x ta x₁) (FHNEHole eps) = wt-filling ta eps
  wt-filling (TACast ta x) FHOuter = _ , TACast ta x
  wt-filling (TACast ta x) (FHCast eps) = wt-filling ta eps
  wt-filling (TAFailedCast x y z w) FHOuter = _ , TAFailedCast x y z w
  wt-filling (TAFailedCast x x₁ x₂ x₃) (FHFailedCast y) = wt-filling x y

  wt-filling (TAFst ta) FHOuter = _ , TAFst ta
  wt-filling (TAFst ta) (FHFst eps) = wt-filling ta eps
  wt-filling (TASnd ta) FHOuter = _ , TASnd ta
  wt-filling (TASnd ta) (FHSnd eps) = wt-filling ta eps
  wt-filling (TAPair ta ta₁) FHOuter = _ ⊗ _ , TAPair ta ta₁
  wt-filling (TAPair ta ta₁) (FHPair1 eps) = wt-filling ta eps
  wt-filling (TAPair ta ta₁) (FHPair2 eps) = wt-filling ta₁ eps

  -- instruction transitions preserve type
  preserve-trans : ∀{ Δ Γ d τ d' } →
            binders-unique d →
            Δ , Γ ⊢ d :: τ →
            d →> d' →
            Δ , Γ ⊢ d' :: τ
  preserve-trans bd TAConst ()
  preserve-trans bd (TAVar x₁) ()
  preserve-trans bd (TALam _ ta) ()
  preserve-trans (BUAp (BULam bd x₁) bd₁ (BDLam x₂ x₃)) (TAAp (TALam apt ta) ta₁) ITLam = lem-subst apt x₂ bd₁ ta ta₁
  preserve-trans bd (TAAp (TACast ta TCRefl) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ TCRefl)) TCRefl
  preserve-trans bd (TAAp (TACast ta (TCArr x x₁)) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ (~sym x))) x₁
  preserve-trans bd (TAEHole x x₁) ()
  preserve-trans bd (TANEHole x ta x₁) ()
  preserve-trans bd (TACast ta x) (ITCastID) = ta
  preserve-trans bd (TACast (TACast ta x) x₁) (ITCastSucceed x₂) = ta
  preserve-trans bd (TACast ta x) (ITGround (MGArr x₁)) = TACast (TACast ta (TCArr TCHole1 TCHole1)) TCHole1
  preserve-trans bd (TACast ta TCHole2) (ITExpand (MGArr x₁)) = TACast (TACast ta TCHole2) (TCArr TCHole2 TCHole2)
  preserve-trans bd (TACast (TACast ta x) x₁) (ITCastFail w y z) = TAFailedCast ta w y z
  preserve-trans bd (TACast ta x) (ITGround (MGProd x₁)) = TACast (TACast ta (TCProd TCHole1 TCHole1)) TCHole1
  preserve-trans bd (TACast ta x) (ITExpand (MGProd x₁)) = TACast (TACast ta TCHole2) (TCProd TCHole2 TCHole2)
  preserve-trans bd (TAFailedCast x y z q) ()
  preserve-trans bd (TAFst (TAPair ta ta₁)) ITFst = ta
  preserve-trans bd (TAFst (TACast ta x)) ITFstCast = TACast (TAFst ta) (~prod1 x)
  preserve-trans bd (TASnd (TAPair ta ta₁)) ITSnd = ta₁
  preserve-trans bd (TASnd (TACast ta x)) ITSndCast = TACast (TASnd ta) (~prod2 x)
  preserve-trans bd (TAPair ta ta₁) ()

  lem-bd-ε1 : ∀{ d ε d0} → d == ε ⟦ d0 ⟧ → binders-unique d → binders-unique d0
  lem-bd-ε1 FHOuter bd = bd
  lem-bd-ε1 (FHAp1 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHAp2 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd₁
  lem-bd-ε1 (FHNEHole eps) (BUNEHole bd x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHCast eps) (BUCast bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHFailedCast eps) (BUFailedCast bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHFst eps) (BUFst bu) = lem-bd-ε1 eps bu
  lem-bd-ε1 (FHSnd eps) (BUSnd bu) = lem-bd-ε1 eps bu
  lem-bd-ε1 (FHPair1 eps) (BUPair bu bu₁ x) = lem-bd-ε1 eps bu
  lem-bd-ε1 (FHPair2 eps) (BUPair bu bu₁ x) = lem-bd-ε1 eps bu₁

  -- this is the main preservation theorem, gluing together the above
  preservation : {Δ : hctx} {d d' : iexp} {τ : typ} {Γ : tctx} →
             binders-unique d →
             Δ , Γ ⊢ d :: τ →
             d ↦ d' →
             Δ , Γ ⊢ d' :: τ
  preservation bd D (Step x x₁ x₂)
    with wt-filling D x
  ... | (_ , wt) = wt-different-fill x D wt (preserve-trans (lem-bd-ε1 x bd) wt x₁) x₂

  -- note that the exact statement of preservation in the paper, where Γ is
  -- empty indicating that the terms are closed, is an immediate corrolary
  -- of the slightly more general statement above.
  preservation' : {Δ : hctx} {d d' : iexp} {τ : typ} →
             binders-unique d →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             Δ , ∅ ⊢ d' :: τ
  preservation' = preservation
