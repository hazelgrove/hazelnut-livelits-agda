open import Nat
open import Prelude
open import core
open import contexts

open import progress
open import htype-decidable
open import lemmas-complete
open import cast-inert

module complete-progress where
  mutual
    lem-comp-boxed→val : {Δ : hctx} {d : ihexp} {τ : htyp} →
                           Δ , ∅ ⊢ d :: τ →
                           d dcomplete →
                           d boxedval →
                           d val
    lem-comp-boxed→val wt dc (BVVal x) = x
    lem-comp-boxed→val wt dc (BVPair bv bv₁) = lem-comp-boxed-prod→val wt dc bv bv₁
    lem-comp-boxed→val wt dc (BVArrCast x bv) with cast-inert dc wt
    lem-comp-boxed→val wt dc (BVArrCast x bv)    | CICast cid       = abort (x refl)
    lem-comp-boxed→val wt (DCCast dc x₁ ()) (BVHoleCast x bv)

    lem-comp-boxed-prod→val : {Δ : hctx} {d1 d2 : ihexp} {τ : htyp} →
                                Δ , ∅ ⊢ ⟨ d1 , d2 ⟩ :: τ →
                                ⟨ d1 , d2 ⟩ dcomplete →
                                d1 boxedval →
                                d2 boxedval →
                                ⟨ d1 , d2 ⟩ val
    lem-comp-boxed-prod→val (TAPair wt1 wt2) dc d1bv d2bv =
      VPair (lem-comp-boxed→val wt1 (lem-comp-pair1 dc) d1bv) (lem-comp-boxed→val wt2 (lem-comp-pair2 dc) d2bv)

  -- as in progress, we define a datatype for the possible outcomes of
  -- progress for readability.
  data okc : (d : ihexp) (Δ : hctx) → Set where
    V : ∀{d Δ} → d val → okc d Δ
    S : ∀{d Δ} → Σ[ d' ∈ ihexp ] (d ↦ d') → okc d Δ

  complete-progress : {Δ : hctx} {d : ihexp} {τ : htyp} →
                       Δ , ∅ ⊢ d :: τ →
                       d dcomplete →
                       okc d Δ
  complete-progress wt comp with progress wt
  complete-progress wt comp | I x = abort (lem-ind-comp comp x)
  complete-progress wt comp | S x = S x
  complete-progress wt comp | BV (BVVal x) = V x
  complete-progress wt comp | BV (BVPair bv1 bv2) = {!!} --  V (lem-comp-boxed-prod→val wt comp bv1 bv2)
  complete-progress wt (DCCast comp x₂ ()) | BV (BVHoleCast x x₁)
  complete-progress (TACast wt x) (DCCast comp x₃ x₄) | BV (BVArrCast x₁ x₂) = abort (x₁ (complete-consistency x x₃ x₄))
