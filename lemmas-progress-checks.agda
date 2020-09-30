open import Nat
open import Prelude
open import core

module lemmas-progress-checks where
  -- boxed values don't have an instruction transition
  boxedval-not-trans : ∀{d d'} → d boxedval → d →> d' → ⊥
  boxedval-not-trans (BVVal VConst) ()
  boxedval-not-trans (BVVal VLam) ()
  boxedval-not-trans (BVArrCast x bv) (ITCastID) = x refl
  boxedval-not-trans (BVHoleCast () bv) (ITCastID)
  boxedval-not-trans (BVHoleCast () bv) (ITCastSucceed x₁)
  boxedval-not-trans (BVHoleCast GHole bv) (ITGround (MGArr x)) = x refl
  boxedval-not-trans (BVHoleCast x a) (ITExpand ())
  boxedval-not-trans (BVHoleCast x x₁) (ITCastFail x₂ () x₄)
  boxedval-not-trans (BVHoleCast GBase bv) (ITGround ())
  boxedval-not-trans (BVHoleCast GProd bv) (ITGround (MGProd x)) = x refl
  boxedval-not-trans (BVProdCast x bv) ITCastID = x refl
  boxedval-not-trans (BVVal (VPair x x₁)) ()
  boxedval-not-trans (BVPair bv bv₁) ()

  -- indets don't have an instruction transition
  indet-not-trans : ∀{d d'} → d indet → d →> d' → ⊥
  indet-not-trans IEHole ()
  indet-not-trans (INEHole x) ()
  indet-not-trans (IAp x₁ () x₂) (ITLam)
  indet-not-trans (IAp x (ICastArr x₁ ind) x₂) (ITApCast ) = x _ _ _ _ _ refl
  indet-not-trans (ICastArr x ind) (ITCastID) = x refl
  indet-not-trans (ICastGroundHole () ind) (ITCastID)
  indet-not-trans (ICastGroundHole x ind) (ITCastSucceed ())
  indet-not-trans (ICastGroundHole GHole ind) (ITGround (MGArr x)) = x refl
  indet-not-trans (ICastHoleGround x ind ()) (ITCastID)
  indet-not-trans (ICastHoleGround x ind x₁) (ITCastSucceed x₂) = x _ _ refl
  indet-not-trans (ICastHoleGround x ind GHole) (ITExpand (MGArr x₂)) = x₂ refl
  indet-not-trans (ICastGroundHole x a) (ITExpand ())
  indet-not-trans (ICastHoleGround x a x₁) (ITGround ())
  indet-not-trans (ICastGroundHole x x₁) (ITCastFail x₂ () x₄)
  indet-not-trans (ICastHoleGround x x₁ x₂) (ITCastFail x₃ x₄ x₅) = x _ _ refl
  indet-not-trans (IFailedCast x x₁ x₂ x₃) ()
  indet-not-trans (ICastGroundHole GBase ind) (ITGround ())
  indet-not-trans (ICastGroundHole GProd ind) (ITGround (MGProd x)) = x refl
  indet-not-trans (ICastHoleGround x ind GBase) (ITExpand ())
  indet-not-trans (ICastHoleGround x ind GProd) (ITExpand (MGProd x₁)) = x₁ refl
  indet-not-trans (IFst (IPair1 ind x) h _) ITFst = h refl
  indet-not-trans (IFst (IPair2 x ind) h _) ITFst = h refl
  indet-not-trans (ISnd (IPair1 ind x) h _) ITSnd = h refl
  indet-not-trans (ISnd (IPair2 x ind) h _) ITSnd = h refl
  indet-not-trans (IPair1 ind x) ()
  indet-not-trans (IPair2 x ind) ()
  indet-not-trans (ICastProd x ind) ITCastID = x refl
  indet-not-trans (IFst (ICastProd x₂ ind) x x₁) ITFstCast = x₁ refl
  indet-not-trans (ISnd (ICastProd x₂ ind) x x₁) ITSndCast = x₁ refl

  -- finals don't have an instruction transition
  final-not-trans : ∀{d d'} → d final → d →> d' → ⊥
  final-not-trans (FBoxedVal x) = boxedval-not-trans x
  final-not-trans (FIndet x) = indet-not-trans x

  -- finals cast from a ground are still final
  final-gnd-cast : ∀{ d τ } → d final → τ ground → (d ⟨ τ ⇒ ⦇·⦈ ⟩) final
  final-gnd-cast (FBoxedVal x) gnd = FBoxedVal (BVHoleCast gnd x)
  final-gnd-cast (FIndet x) gnd = FIndet (ICastGroundHole gnd x)

  -- if an expression results from filling a hole in an evaluation context,
  -- the hole-filler must have been final
  final-sub-final : ∀{d ε x} → d final → d == ε ⟦ x ⟧ → x final
  final-sub-final x FHOuter = x
  final-sub-final (FBoxedVal (BVVal ())) (FHAp1 eps)
  final-sub-final (FBoxedVal (BVVal ())) (FHAp2 eps)
  final-sub-final (FBoxedVal (BVVal ())) (FHNEHole eps)
  final-sub-final (FBoxedVal (BVVal ())) (FHCast eps)
  final-sub-final (FBoxedVal (BVVal ())) (FHFailedCast y)
  final-sub-final (FBoxedVal (BVArrCast x₁ x₂)) (FHCast eps) = final-sub-final (FBoxedVal x₂) eps
  final-sub-final (FBoxedVal (BVHoleCast x₁ x₂)) (FHCast eps) = final-sub-final (FBoxedVal x₂) eps
  final-sub-final (FBoxedVal (BVVal ())) (FHFst eps)
  final-sub-final (FBoxedVal (BVVal ())) (FHSnd eps)
  final-sub-final (FBoxedVal (BVVal (VPair x₁ x₂))) (FHPair1 eps) = final-sub-final (FBoxedVal (BVVal x₁)) eps
  final-sub-final (FBoxedVal (BVVal (VPair x₁ x₂))) (FHPair2 eps) = final-sub-final (FBoxedVal (BVVal x₂)) eps
  final-sub-final (FBoxedVal (BVProdCast x₁ x₂)) (FHCast eps) = final-sub-final (FBoxedVal x₂) eps
  final-sub-final (FIndet (IAp x₁ x₂ x₃)) (FHAp1 eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (IAp x₁ x₂ x₃)) (FHAp2 eps) = final-sub-final x₃ eps
  final-sub-final (FIndet (INEHole x₁)) (FHNEHole eps) = final-sub-final x₁ eps
  final-sub-final (FIndet (ICastArr x₁ x₂)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (ICastGroundHole x₁ x₂)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (ICastHoleGround x₁ x₂ x₃)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (IFailedCast x₁ x₂ x₃ x₄)) (FHFailedCast y) = final-sub-final x₁ y
  final-sub-final (FIndet (IFst x₁ _ x₂)) (FHFst eps) = final-sub-final (FIndet x₁) eps
  final-sub-final (FIndet (ISnd x₁ _ x₂)) (FHSnd eps) = final-sub-final (FIndet x₁) eps
  final-sub-final (FIndet (IPair1 x₁ x₂)) (FHPair1 eps) = final-sub-final (FIndet x₁) eps
  final-sub-final (FIndet (IPair2 x₁ x₂)) (FHPair1 eps) = final-sub-final x₁ eps
  final-sub-final (FIndet (IPair1 x₁ x₂)) (FHPair2 eps) = final-sub-final x₂ eps
  final-sub-final (FIndet (IPair2 x₁ x₂)) (FHPair2 eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FIndet (ICastProd x₁ x₂)) (FHCast eps) = final-sub-final (FIndet x₂) eps
  final-sub-final (FBoxedVal (BVPair x₁ x₂)) (FHPair1 eps) = final-sub-final (FBoxedVal x₁) eps
  final-sub-final (FBoxedVal (BVPair x₁ x₂)) (FHPair2 eps) = final-sub-final (FBoxedVal x₂) eps

  final-sub-not-trans : ∀{d d' d'' ε} →  d final → d == ε ⟦ d' ⟧ → d' →> d'' → ⊥
  final-sub-not-trans f sub step = final-not-trans (final-sub-final f sub) step
