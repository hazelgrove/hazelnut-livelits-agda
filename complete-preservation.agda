open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-complete
open import preservation

module complete-preservation where
  -- if you substitute a complete term into a complete term, the result is
  -- still complete.
  cp-subst : ∀ {x d1 d2} →
           d1 dcomplete →
           d2 dcomplete →
           ([ d2 / x ] d1) dcomplete
  cp-subst {x = y} (DCVar {x = x}) dc2 with natEQ x y
  cp-subst DCVar dc2 | Inl refl = dc2
  cp-subst DCVar dc2 | Inr x₂ = DCVar
  cp-subst DCConst dc2 = DCConst
  cp-subst {x = x} (DCLam {x = y} dc1 x₂) dc2 with natEQ y x
  cp-subst (DCLam dc1 x₃) dc2 | Inl refl = DCLam dc1 x₃
  cp-subst (DCLam dc1 x₃) dc2 | Inr x₂ = DCLam (cp-subst dc1 dc2) x₃
  cp-subst (DCAp dc1 dc2) dc3 = DCAp (cp-subst dc1 dc3) (cp-subst dc2 dc3)
  cp-subst (DCCast dc1 x₁ x₂) dc2 = DCCast (cp-subst dc1 dc2) x₁ x₂
  cp-subst (DCFst dc1) dc2 = DCFst (cp-subst dc1 dc2)
  cp-subst (DCSnd dc1) dc2 = DCSnd (cp-subst dc1 dc2)
  cp-subst (DCPair dc1 dc3) dc2 = DCPair (cp-subst dc1 dc2) (cp-subst dc3 dc2)

  -- this just lets me pull the particular x out of a derivation; it's not
  -- bound in any of the constructors explicitly since it's only in the
  -- lambda case; so below i have no idea how else to get a name for it,
  -- instead of leaving it dotted in the context
  lem-proj : {x : Nat} {d : iexp} { τ : typ} → (·λ_[_]_ x τ d) dcomplete → Σ[ y ∈ Nat ] (y == x)
  lem-proj {x} (DCLam dc x₁) = x , refl

  -- a complete well typed term steps to a complete term.
  cp-rhs : ∀{d τ d' Δ} →
             d dcomplete →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             d' dcomplete
  cp-rhs dc TAConst (Step FHOuter () FHOuter)
  cp-rhs dc (TAVar x₁) stp = abort (somenotnone (! x₁))
  cp-rhs dc (TALam _ wt) (Step FHOuter () FHOuter)
  -- this case is a little more complicated than it feels like it ought to
  -- be, just from horsing around with agda implicit variables.
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step FHOuter ITLam FHOuter) with lem-proj dc
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step FHOuter ITLam FHOuter) | x , refl with cp-subst {x = x} dc dc₁
  ... | qq with natEQ x x
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step FHOuter ITLam FHOuter) | x , refl | DCLam qq x₁ | Inl refl = cp-subst qq dc₁
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step FHOuter ITLam FHOuter) | x , refl | qq | Inr x₁ = abort (x₁ refl)
  cp-rhs (DCAp (DCCast dc (TCArr x x₁) (TCArr x₂ x₃)) dc₁) (TAAp (TACast wt x₄) wt₁) (Step FHOuter ITApCast FHOuter) = DCCast (DCAp dc (DCCast dc₁ x₂ x)) x₁ x₃
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step (FHAp1 x) x₁ (FHAp1 x₂)) = DCAp (cp-rhs dc wt (Step x x₁ x₂)) dc₁
  cp-rhs (DCAp dc dc₁) (TAAp wt wt₁) (Step (FHAp2 x) x₁ (FHAp2 x₂)) = DCAp dc (cp-rhs dc₁ wt₁ (Step x x₁ x₂))
  cp-rhs () (TAEHole x x₁) stp
  cp-rhs () (TANEHole x wt x₁) stp
  cp-rhs (DCCast dc x x₁) (TACast wt x₂) (Step FHOuter ITCastID FHOuter) = dc
  cp-rhs (DCCast dc () x₁) (TACast wt x₂) (Step FHOuter (ITCastSucceed x₃) FHOuter)
  cp-rhs (DCCast dc () x₁) (TACast wt x₂) (Step FHOuter (ITCastFail x₃ x₄ x₅) FHOuter)
  cp-rhs (DCCast dc x ()) (TACast wt x₂) (Step FHOuter (ITGround x₃) FHOuter)
  cp-rhs (DCCast dc () x₁) (TACast wt x₂) (Step FHOuter (ITExpand x₃) FHOuter)
  cp-rhs (DCCast dc x x₁) (TACast wt x₂) (Step (FHCast x₃) x₄ (FHCast x₅)) = DCCast (cp-rhs dc wt (Step x₃ x₄ x₅)) x x₁
  cp-rhs () (TAFailedCast wt x x₁ x₂) stp
  cp-rhs (DCFst dc) (TAFst wt) (Step FHOuter ITFst FHOuter) = lem-comp-pair1 dc
  cp-rhs (DCFst (DCCast dc x₁ x₂)) (TAFst (TACast wt x)) (Step FHOuter ITFstCast FHOuter) = DCCast (DCFst dc) (lem-comp-prod1 x₁) (lem-comp-prod1 x₂)
  cp-rhs (DCFst dc) (TAFst wt) (Step (FHFst x) x₁ (FHFst x₂)) = DCFst (cp-rhs dc wt (Step x x₁ x₂))
  cp-rhs (DCSnd dc) (TASnd wt) (Step FHOuter ITSnd FHOuter) = lem-comp-pair2 dc
  cp-rhs (DCSnd (DCCast dc x₁ x₂)) (TASnd (TACast wt x)) (Step FHOuter ITSndCast FHOuter) = DCCast (DCSnd dc) (lem-comp-prod2 x₁) (lem-comp-prod2 x₂)
  cp-rhs (DCSnd dc) (TASnd wt) (Step (FHSnd x) x₁ (FHSnd x₂)) = DCSnd (cp-rhs dc wt (Step x x₁ x₂))
  cp-rhs (DCPair dc dc₁) (TAPair wt wt₁) (Step FHOuter () FHOuter)
  cp-rhs (DCPair dc dc₁) (TAPair wt wt₁) (Step (FHPair1 x) x₁ (FHPair1 x₂)) = DCPair (cp-rhs dc wt (Step x x₁ x₂)) dc₁
  cp-rhs (DCPair dc dc₁) (TAPair wt wt₁) (Step (FHPair2 x) x₁ (FHPair2 x₂)) = DCPair dc (cp-rhs dc₁ wt₁ (Step x x₁ x₂))

  -- this is the main result of this file.
  complete-preservation : ∀{d τ d' Δ} →
             binders-unique d →
             d dcomplete →
             Δ , ∅ ⊢ d :: τ →
             d ↦ d' →
             (Δ , ∅ ⊢ d' :: τ) × (d' dcomplete)
  complete-preservation bd dc wt stp = preservation bd wt stp , cp-rhs dc wt stp
