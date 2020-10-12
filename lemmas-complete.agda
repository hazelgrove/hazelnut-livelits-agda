open import Nat
open import Prelude
open import core

open import lemmas-gcomplete

module lemmas-complete where
  lem-comp-pair1 : ∀{d1 d2} → ⟨ d1 , d2 ⟩ dcomplete → d1 dcomplete
  lem-comp-pair1 (DCPair h _) = h

  lem-comp-pair2 : ∀{d1 d2} → ⟨ d1 , d2 ⟩ dcomplete → d2 dcomplete
  lem-comp-pair2 (DCPair _ h) = h

  lem-comp-prod1 : ∀{τ1 τ2} → τ1 ⊗ τ2 tcomplete → τ1 tcomplete
  lem-comp-prod1 (TCProd h _) = h

  lem-comp-prod2 : ∀{τ1 τ2} → τ1 ⊗ τ2 tcomplete → τ2 tcomplete
  lem-comp-prod2 (TCProd _ h) = h

  -- no term is both complete and indeterminate
  lem-ind-comp : ∀{d} → d dcomplete → d indet → ⊥
  lem-ind-comp DCVar ()
  lem-ind-comp DCConst ()
  lem-ind-comp (DCLam comp x₁) ()
  lem-ind-comp (DCAp comp comp₁) (IAp x ind x₁) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastArr x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastGroundHole x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastHoleGround x₂ ind x₃) = lem-ind-comp comp ind
  lem-ind-comp (DCCast dc x x₁) (ICastProd x₂ ind) = lem-ind-comp dc ind
  lem-ind-comp (DCFst d) (IFst ind x x₁) = lem-ind-comp d ind
  lem-ind-comp (DCSnd d) (ISnd ind x x₁) = lem-ind-comp d ind
  lem-ind-comp (DCPair d d₁) (IPair1 ind x) = lem-ind-comp d ind
  lem-ind-comp (DCPair d d₁) (IPair2 x ind) = lem-ind-comp d₁ ind

  -- complete types that are consistent are equal
  complete-consistency : ∀{τ1 τ2} → τ1 ~ τ2 → τ1 tcomplete → τ2 tcomplete → τ1 == τ2
  complete-consistency TCRefl TCBase comp2 = refl
  complete-consistency TCRefl (TCArr comp1 comp2) comp3 = refl
  complete-consistency TCHole1 comp1 ()
  complete-consistency TCHole2 () comp2
  complete-consistency (TCArr consis consis₁) (TCArr comp1 comp2) (TCArr comp3 comp4)
   with complete-consistency consis comp1 comp3 | complete-consistency consis₁ comp2 comp4
  ... | refl | refl = refl
  complete-consistency TCRefl (TCProd tc' tc'') = λ _ → refl
  complete-consistency (TCProd tc tc') (TCProd tc1 tc2) (TCProd tc3 tc4)
    with complete-consistency tc tc1 tc3 | complete-consistency tc' tc2 tc4
  ... | refl | refl = refl

  -- a well typed complete term is assigned a complete type
  complete-ta : ∀{Γ Δ d τ} → (Γ gcomplete) →
                             (Δ , Γ ⊢ d :: τ) →
                             d dcomplete →
                             τ tcomplete
  complete-ta gc TAConst comp = TCBase
  complete-ta gc (TAVar x₁) DCVar = gc _ _ x₁
  complete-ta gc (TALam a wt) (DCLam comp x₁) = TCArr x₁ (complete-ta (gcomp-extend gc x₁ a ) wt comp)
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁) with complete-ta gc wt comp
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁) | TCArr qq qq₁ = qq₁
  complete-ta gc (TAEHole x x₁) ()
  complete-ta gc (TANEHole x wt x₁) ()
  complete-ta gc (TACast wt x) (DCCast comp x₁ x₂) = x₂
  complete-ta gc (TAFailedCast wt x x₁ x₂) ()
  complete-ta gc (TAFst wt) (DCFst comp) = lem-comp-prod1 (complete-ta gc wt comp)
  complete-ta gc (TASnd wt) (DCSnd comp) = lem-comp-prod2 (complete-ta gc wt comp)
  complete-ta gc (TAPair ta ta₁) (DCPair comp comp₁) = TCProd (complete-ta gc ta comp) (complete-ta gc ta₁ comp₁)

  -- a well typed term synthesizes a complete type
  comp-synth : ∀{Γ e τ} →
                   Γ gcomplete →
                   e ecomplete →
                   Γ ⊢ e => τ →
                   τ tcomplete
  comp-synth gc ec SConst = TCBase
  comp-synth gc (ECAsc x ec) (SAsc x₁) = x
  comp-synth gc ec (SVar x) = gc _ _ x
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAHole x₁) with comp-synth gc ec wt
  ... | ()
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAArr x₁) with comp-synth gc ec wt
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAArr x₁) | TCArr qq qq₁ = qq₁
  comp-synth gc () SEHole
  comp-synth gc () (SNEHole _ wt)
  comp-synth gc (ECLam2 ec x₁) (SLam x₂ wt) = TCArr x₁ (comp-synth (gcomp-extend gc x₁ x₂) ec wt)
  comp-synth gc (ECFst ec) (SFst wt MPHole) = comp-synth gc ec wt
  comp-synth gc (ECFst ec) (SFst wt MPProd) = lem-comp-prod1 (comp-synth gc ec wt)
  comp-synth gc (ECSnd ec) (SSnd wt MPHole) = comp-synth gc ec wt
  comp-synth gc (ECSnd ec) (SSnd wt MPProd) = lem-comp-prod2 (comp-synth gc ec wt)
  comp-synth gc (ECPair ec ec₁) (SPair x wt wt₁) = TCProd (comp-synth gc ec wt) (comp-synth gc ec₁ wt₁)

  -- complete boxed values are just values
  lem-comp-boxed-val : {Δ : hctx} {d : iexp} {τ : typ} {Γ : tctx} →
                           Δ , Γ ⊢ d :: τ →
                           d dcomplete →
                           d boxedval →
                           d val
  lem-comp-boxed-val wt comp (BVVal VConst) = VConst
  lem-comp-boxed-val wt comp (BVVal VLam) = VLam
  lem-comp-boxed-val wt comp (BVVal (VPair x x₁)) = VPair x x₁
  lem-comp-boxed-val (TAPair wt wt₁) (DCPair comp comp₁) (BVPair bv bv₁) = VPair (lem-comp-boxed-val wt comp bv)
                                                                                 (lem-comp-boxed-val wt₁ comp₁ bv₁)
  lem-comp-boxed-val (TACast wt x₃) (DCCast comp x₁ x₂) (BVArrCast x bv) = abort (x (complete-consistency x₃ x₁ x₂))
  lem-comp-boxed-val (TACast wt x₁) (DCCast comp x₂ x₃) (BVProdCast x bv) = abort (x (complete-consistency x₁ x₂ x₃))
  lem-comp-boxed-val (TACast wt x₁) (DCCast comp x₂ ()) (BVHoleCast x bv)
