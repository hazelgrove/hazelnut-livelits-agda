open import Nat
open import Prelude
open import core
open import contexts
open import typed-elaboration
open import lemmas-gcomplete
open import lemmas-complete

module complete-elaboration where
  mutual
    complete-elaboration-synth : ∀{e τ Γ Δ d} →
                               Γ gcomplete →
                               e ecomplete →
                               Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                               (d dcomplete × τ tcomplete × Δ == ∅)
    complete-elaboration-synth gc ec ESConst = DCConst , TCBase , refl
    complete-elaboration-synth gc ec (ESVar x₁) = DCVar , gc _ _ x₁ , refl
    complete-elaboration-synth gc (ECLam2 ec x₁) (ESLam x₂ exp)
      with complete-elaboration-synth (gcomp-extend gc x₁ x₂) ec exp
    ... | ih1 , ih2 , ih3 = DCLam ih1 x₁ , TCArr x₁ ih2 , ih3
    complete-elaboration-synth gc (ECAp ec ec₁) (ESAp _ _ x MAHole x₂ x₃)
      with comp-synth gc ec x
    ... | ()
    complete-elaboration-synth gc (ECAp ec ec₁) (ESAp {Δ1 = Δ1} {Δ2 = Δ2} _ _ x MAArr x₂ x₃)
      with comp-synth gc ec x
    ... | TCArr t1 t2
      with complete-elaboration-ana gc ec (TCArr t1 t2) x₂ | complete-elaboration-ana gc ec₁ t1 x₃
    ... | ih1 , _ ,  ih4 | ih2 , _ , ih3 = DCAp (DCCast ih1 (comp-ana gc x₂ ih1) (TCArr t1 t2)) (DCCast ih2 (comp-ana gc x₃ ih2) t1) ,
                                  t2 ,
                                  tr (λ qq → (qq ∪ Δ2) == ∅) (! ih4) (tr (λ qq → (∅ ∪ qq) == ∅) (! ih3) refl)
    complete-elaboration-synth gc () ESEHole
    complete-elaboration-synth gc () (ESNEHole _ exp)
    complete-elaboration-synth gc (ECAsc x ec) (ESAsc x₁)
      with complete-elaboration-ana gc ec x x₁
    ... | ih1 , _ , ih2 = DCCast ih1 (comp-ana gc x₁ ih1) x , x , ih2
    complete-elaboration-synth gc (ECFst ec) (ESFst x x₁ x₂)
      with comp-synth gc ec x
    complete-elaboration-synth gc (ECFst ec) (ESFst x () x₂)     | TCBase
    complete-elaboration-synth gc (ECFst ec) (ESFst x () x₂)     | TCArr _ _
    complete-elaboration-synth gc (ECFst ec) (ESFst x MPProd x₂) | tc with complete-elaboration-ana gc ec tc x₂
    complete-elaboration-synth gc (ECFst ec) (ESFst x MPProd x₂) | tc | ih1 , ih2 , ih3 = DCFst (DCCast ih1 ih2 tc) , lem-comp-prod1 tc , ih3
    complete-elaboration-synth gc (ECSnd ec) (ESSnd x x₁ x₂)
      with comp-synth gc ec x
    complete-elaboration-synth gc (ECSnd ec) (ESSnd x () x₂)     | TCBase
    complete-elaboration-synth gc (ECSnd ec) (ESSnd x () x₂)     | TCArr _ _
    complete-elaboration-synth gc (ECSnd ec) (ESSnd x MPProd x₂) | tc with complete-elaboration-ana gc ec tc x₂
    complete-elaboration-synth gc (ECSnd ec) (ESSnd x MPProd x₂) | tc | ih1 , ih2 , ih3 = DCSnd (DCCast ih1 ih2 tc) , lem-comp-prod2 tc , ih3
    complete-elaboration-synth gc (ECPair ec1 ec2) (ESPair _ _ es1 es2)
      with complete-elaboration-synth gc ec1 es1 | complete-elaboration-synth gc ec2 es2
    ... | dc1 , tc1 , refl | dc2 , tc2 , refl = DCPair dc1 dc2 , TCProd tc1 tc2 , refl

    complete-elaboration-ana : ∀{e τ τ' Γ Δ d} →
                             Γ gcomplete →
                             e ecomplete →
                             τ tcomplete →
                             Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                             (d dcomplete × τ' tcomplete × Δ == ∅)
    complete-elaboration-ana gc (ECLam1 ec) () (EALam x₁ MAHole exp)
    complete-elaboration-ana gc (ECLam1 ec) (TCArr t1 t2)  (EALam x₁ MAArr exp)
      with complete-elaboration-ana (gcomp-extend gc t1 x₁) ec t2 exp
    ... | ih , ih3 , ih2 = DCLam ih t1 , TCArr t1 ih3 , ih2
    complete-elaboration-ana gc ec tc (EASubsume x x₁ x₂ x₃) = complete-elaboration-synth gc ec x₂

    -- this is just a convenience since it shows up a few times above
    comp-ana : ∀{Γ e τ d τ' Δ} →
       Γ gcomplete →
       Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
       d dcomplete →
       τ' tcomplete
    comp-ana gc ex dc = complete-ta gc (π2 (typed-elaboration-ana ex)) dc
