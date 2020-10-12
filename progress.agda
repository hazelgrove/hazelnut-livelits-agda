open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-consistency
open import lemmas-ground

open import progress-checks

open import canonical-boxed-forms
open import canonical-value-forms
open import canonical-indeterminate-forms

open import ground-decidable
open import typ-dec

module progress where
  -- this is a little bit of syntactic sugar to avoid many layer nested Inl
  -- and Inrs that you would get from the more literal transcription of the
  -- consequent of progress
  data ok : (d : iexp) (Δ : hctx) → Set where
    S  : ∀{d Δ} → Σ[ d' ∈ iexp ] (d ↦ d') → ok d Δ
    I  : ∀{d Δ} → d indet → ok d Δ
    BV : ∀{d Δ} → d boxedval → ok d Δ

  progress : {Δ : hctx} {d : iexp} {τ : typ} →
             Δ , ∅ ⊢ d :: τ →
             ok d Δ
    -- constants
  progress TAConst = BV (BVVal VConst)

    -- variables
  progress (TAVar x₁) = abort (somenotnone (! x₁))

    -- lambdas
  progress (TALam _ wt) = BV (BVVal VLam)

    -- applications
  progress (TAAp wt1 wt2)
    with progress wt1 | progress wt2
    -- if the left steps, the whole thing steps
  progress (TAAp wt1 wt2) | S (_ , Step x y z) | _ = S (_ , Step (FHAp1 x) y (FHAp1 z))
    -- if the left is indeterminate, step the right
  progress (TAAp wt1 wt2) | I i | S (_ , Step x y z) = S (_ , Step (FHAp2 x) y (FHAp2  z))
    -- if they're both indeterminate, step when the cast steps and indet otherwise
  progress (TAAp wt1 wt2) | I x | I x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress (TAAp wt1 wt2) | I x | I y | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | I x | I y | CIFAEHole (_ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFANEHole (_ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFAFst (_ , _ , refl , _)                   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  progress (TAAp wt1 wt2) | I x | I y | CIFASnd (_ , _ , refl , _)                   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
    -- similar if the left is indetermiante but the right is a boxed val
  progress (TAAp wt1 wt2) | I x | BV x₁
    with canonical-indeterminate-forms-arr wt1 x
  progress (TAAp wt1 wt2) | I x | BV y | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | I x | BV y | CIFAEHole (_ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFANEHole (_ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFAFst (_ , _ , refl , _)                   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  progress (TAAp wt1 wt2) | I x | BV y | CIFASnd (_ , _ , refl , _)                   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
    -- if the left is a boxed value, inspect the right
  progress (TAAp wt1 wt2) | BV v | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  progress (TAAp wt1 wt2) | BV v | I i
    with canonical-boxed-forms-arr wt1 v
  ... | CBFLam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFCastArr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | BV v | BV v₂
    with canonical-boxed-forms-arr wt1 v
  ... | CBFLam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFCastArr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)

    -- empty holes are indeterminate
  progress (TAEHole _ _ ) = I IEHole

    -- nonempty holes step if the innards step, indet otherwise
  progress (TANEHole xin wt x₁)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHNEHole x) y (FHNEHole z))
  ... | I  x = I (INEHole (FIndet x))
  ... | BV x = I (INEHole (FBoxedVal x))

  -- products : fst
  progress (TAFst wt)
    with progress wt
  progress (TAFst wt) | S (_ , Step fh1 it fh2) = S (_ , Step (FHFst fh1) it (FHFst fh2))
  progress (TAFst wt) | I h
    with canonical-indeterminate-forms-prod wt h
  progress (TAFst wt) | I h | CIFPEHole (_ , _ , _ , refl , _)             = I (IFst h (λ ()) (λ ()))
  progress (TAFst wt) | I h | CIFPNEHole (_ , _ , _ , _ , _ , refl , _)    = I (IFst h (λ ()) (λ ()))
  progress (TAFst wt) | I h | CIFPAp (_ , _ , _ , _ , _ , refl , _)        = I (IFst h (λ ()) (λ ()))
  progress (TAFst wt) | I h | CIFPFst (_ , _ , refl , _)                   = I (IFst h (λ ()) (λ ()))
  progress (TAFst wt) | I h | CIFPSnd (_ , _ , refl , _)                   = I (IFst h (λ ()) (λ ()))
  progress (TAFst wt) | I h | CIFPPair1 (_ , _ , refl , _ )                = S (_ , Step FHOuter ITFst FHOuter)
  progress (TAFst wt) | I h | CIFPPair2 (_ , _ , refl , _ )                = S (_ , Step FHOuter ITFst FHOuter)
  progress (TAFst wt) | I h | CIFPCast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITFstCast FHOuter)
  progress (TAFst wt) | I h | CIFPCastHole (_ , refl , refl , refl , _ )   = I (IFst h (λ ()) (λ ()))
  progress (TAFst wt) | I h | CIFPFailedCast (_ , _ , refl , _ )           = I (IFst h (λ ()) (λ ()))
  progress (TAFst wt) | BV h
    with canonical-boxed-forms-prod wt h
  progress (TAFst wt) | BV h | CBFPairVal (_ , _ , refl , _ , _)         = S (_ , Step FHOuter ITFst FHOuter)
  progress (TAFst wt) | BV h | CBFPairBV (_ , _ , refl , _ , _)          = S (_ , Step FHOuter ITFst FHOuter)
  progress (TAFst wt) | BV h | CBFCastProd (_ , _ , _ , refl , _) = S (_ , Step FHOuter ITFstCast FHOuter)

  -- products : snd
  progress (TASnd wt)
    with progress wt
  progress (TASnd wt) | S (_ , Step fh1 it fh2) = S (_ , Step (FHSnd fh1) it (FHSnd fh2))
  progress (TASnd wt) | I h
    with canonical-indeterminate-forms-prod wt h
  progress (TASnd wt) | I h | CIFPEHole (_ , _ , _ , refl , _)             = I (ISnd h (λ ()) (λ ()))
  progress (TASnd wt) | I h | CIFPNEHole (_ , _ , _ , _ , _ , refl , _)    = I (ISnd h (λ ()) (λ ()))
  progress (TASnd wt) | I h | CIFPAp (_ , _ , _ , _ , _ , refl , _)        = I (ISnd h (λ ()) (λ ()))
  progress (TASnd wt) | I h | CIFPFst (_ , _ , refl , _)                   = I (ISnd h (λ ()) (λ ()))
  progress (TASnd wt) | I h | CIFPSnd (_ , _ , refl , _)                   = I (ISnd h (λ ()) (λ ()))
  progress (TASnd wt) | I h | CIFPPair1 (_ , _ , refl , _ )                = S (_ , Step FHOuter ITSnd FHOuter)
  progress (TASnd wt) | I h | CIFPPair2 (_ , _ , refl , _ )                = S (_ , Step FHOuter ITSnd FHOuter)
  progress (TASnd wt) | I h | CIFPCast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITSndCast FHOuter)
  progress (TASnd wt) | I h | CIFPCastHole (_ , refl , refl , refl , _ )   = I (ISnd h (λ ()) (λ ()))
  progress (TASnd wt) | I h | CIFPFailedCast (_ , _ , refl , _ )           = I (ISnd h (λ ()) (λ ()))
  progress (TASnd wt) | BV h
    with canonical-boxed-forms-prod wt h
  progress (TASnd wt) | BV h | CBFPairVal (_ , _ , refl , _ )         = S (_ , Step FHOuter ITSnd FHOuter)
  progress (TASnd wt) | BV h | CBFPairBV (_ , _ , refl , _ )          = S (_ , Step FHOuter ITSnd FHOuter)
  progress (TASnd wt) | BV h | CBFCastProd (_ , _ , _ , refl , _) = S (_ , Step FHOuter ITSndCast FHOuter)

  -- products : pairs
  progress (TAPair wt1 wt2)
    with progress wt1 | progress wt2
  progress (TAPair wt1 wt2) | S (_ , Step fh1 it fh2) | _    = S (_ , Step (FHPair1 fh1) it (FHPair1 fh2))
  progress (TAPair wt1 wt2) | I x | S (_ , Step fh1 it fh2)  = S (_ , Step (FHPair2 fh1) it (FHPair2 fh2))
  progress (TAPair wt1 wt2) | I x | I x₁                     = I (IPair1 x (FIndet x₁))
  progress (TAPair wt1 wt2) | I x | BV x₁                    = I (IPair1 x (FBoxedVal x₁))
  progress (TAPair wt1 wt2) | BV x | S (_ , Step fh1 it fh2) = S (_ , Step (FHPair2 fh1) it (FHPair2 fh2))
  progress (TAPair wt1 wt2) | BV x | I x₁                    = I (IPair2 (FBoxedVal x) x₁)
  progress (TAPair wt1 wt2) | BV x | BV x₁                   = BV (BVPair x x₁)

    -- casts
  progress (TACast wt con)
    with progress wt
    -- step if the innards step
  progress (TACast wt con) | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
    -- if indet, inspect how the types in the cast are realted by consistency:
    -- if they're the same, step by ID
  progress (TACast wt TCRefl)  | I x = S (_ , Step FHOuter ITCastID FHOuter)
    -- if first type is hole
  progress (TACast {τ1 = τ1} wt TCHole1) | I x
    with τ1
  progress (TACast wt TCHole1) | I x | b = I (ICastGroundHole GBase x)
  progress (TACast wt TCHole1) | I x | ⦇·⦈ = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole1) | I x | τ11 ==> τ12
    with ground-decidable (τ11 ==> τ12)
  progress (TACast wt TCHole1) | I x₁ | .⦇·⦈ ==> .⦇·⦈ | Inl GHole = I (ICastGroundHole GHole x₁)
  progress (TACast wt TCHole1) | I x₁ | τ11 ==> τ12 | Inr x =  S (_ , Step FHOuter (ITGround (MGArr (ground-arr-not-hole x))) FHOuter)
  progress (TACast wt TCHole1) | I x | τ11 ⊗ τ12
    with ground-decidable (τ11 ⊗ τ12)
  progress (TACast wt TCHole1) | I x | τ11 ⊗ τ12 | Inl x₁ = I (ICastGroundHole x₁ x)
  progress (TACast wt TCHole1) | I x | τ11 ⊗ τ12 | Inr x₁ = S (_ , Step FHOuter (ITGround (MGProd (ground-prod-not-hole x₁))) FHOuter)
    -- if second type is hole
  progress (TACast wt (TCHole2 {b})) | I x
    with canonical-indeterminate-forms-hole wt x
  progress (TACast wt (TCHole2 {b})) | I x | CIFHEHole (_ , _ , _ , refl , f)           = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHNEHole (_ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHAp (_ , _ , _ , refl , _ )             = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHFst (_ , _ , refl , _)                 = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHSnd (_ , _ , refl , _)                 = I (ICastHoleGround (λ _ _ ()) x GBase)
  progress (TACast wt (TCHole2 {b})) | I x | CIFHCast (_ , τ , refl , _)
    with typ-dec τ b
  progress (TACast wt (TCHole2 {b})) | I x₁ | CIFHCast (_ , .b , refl , _ , grn , _) | Inl refl = S (_ , Step FHOuter (ITCastSucceed grn ) FHOuter)
  progress (TACast wt (TCHole2 {b})) | I x₁ | CIFHCast (_ , _ , refl , π2 , grn , _)  | Inr x =    S (_ , Step FHOuter (ITCastFail grn GBase x) FHOuter)
  progress (TACast wt (TCHole2 {⦇·⦈}))| I x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCHole2 {τ11 ==> τ12})) | I x
    with ground-decidable (τ11 ==> τ12)
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x₁ | Inl GHole
    with canonical-indeterminate-forms-hole wt x₁
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x | Inl GHole | CIFHEHole (_ , _ , _ , refl , _)          = I (ICastHoleGround (λ _ _ ()) x GHole)
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x | Inl GHole | CIFHNEHole (_ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ _ _ ()) x GHole)
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x | Inl GHole | CIFHAp (_ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GHole)
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x | Inl GHole | CIFHFst (_ , _ , refl , _)                = I (ICastHoleGround (λ _ _ ()) x GHole)
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x | Inl GHole | CIFHSnd (_ , _ , refl , _)                = I (ICastHoleGround (λ _ _ ()) x GHole)
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x | Inl GHole | CIFHCast (_ , _ , refl , _ , GBase , _)   = S (_ , Step FHOuter (ITCastFail GBase GHole (λ ())) FHOuter )
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x | Inl GHole | CIFHCast (_ , _ , refl , _ , GHole , _)   = S (_ , Step FHOuter (ITCastSucceed GHole) FHOuter)
  progress (TACast wt (TCHole2 {.⦇·⦈ ==> .⦇·⦈})) | I x | Inl GHole | CIFHCast (_ , _ , refl , _ , GProd , _)   = S (_ , Step FHOuter (ITCastFail GProd GHole (λ ())) FHOuter )
  progress (TACast wt (TCHole2 {τ11 ==> τ12})) | I x₁ | Inr x = S (_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole x))) FHOuter)
  progress (TACast wt (TCHole2 {τ11 ⊗ τ12}))   | I x
    with ground-decidable (τ11 ⊗ τ12)
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd
    with canonical-indeterminate-forms-hole wt x
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd | CIFHEHole (_ , _ , _ , refl , _)          = I (ICastHoleGround (λ _ _ ()) x GProd)
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd | CIFHNEHole (_ , _ , _ , _ , _ , refl , _) = I (ICastHoleGround (λ _ _ ()) x GProd)
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd | CIFHAp (_ , _ , _ , refl , _ )            = I (ICastHoleGround (λ _ _ ()) x GProd)
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd | CIFHFst (_ , _ , refl , _)                = I (ICastHoleGround (λ _ _ ()) x GProd)
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd | CIFHSnd (_ , _ , refl , _)                = I (ICastHoleGround (λ _ _ ()) x GProd)
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd | CIFHCast (_ , _ , refl , _ , GBase , _)   = S (_ , Step FHOuter (ITCastFail GBase GProd λ ()) FHOuter )
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd | CIFHCast (_ , _ , refl , _ , GHole , _)   = S (_ , Step FHOuter (ITCastFail GHole GProd λ ()) FHOuter)
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inl GProd | CIFHCast (_ , _ , refl , _ , GProd , _)   = S (_ , Step FHOuter (ITCastSucceed GProd) FHOuter )
  progress (TACast wt (TCHole2 {.(_ ⊗ _)})) | I x | Inr h = S (_ , Step FHOuter (ITExpand (MGProd (ground-prod-not-hole h))) FHOuter)
    -- if both are arrows
  progress (TACast wt (TCArr {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | I x
    with typ-dec (τ1 ==> τ2)  (τ1' ==> τ2')
  progress (TACast wt (TCArr c1 c2)) | I x₁ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCArr c1 c2)) | I x₁ | Inr x = I (ICastArr x x₁)
    -- if both are products
  progress (TACast wt (TCProd {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | I x
    with typ-dec (τ1 ⊗ τ2) (τ1' ⊗ τ2')
  progress (TACast wt (TCProd c1 c2)) | I x  | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCProd c1 c2)) | I h1 | Inr h2   = I (ICastProd h2 h1)
    -- boxed value cases, inspect how the casts are realted by consistency
    -- step by ID if the casts are the same
  progress (TACast wt TCRefl)  | BV x = S (_ , Step FHOuter ITCastID FHOuter)
    -- if left is hole
  progress (TACast wt (TCHole1 {τ = τ})) | BV x
    with ground-decidable τ
  progress (TACast wt TCHole1) | BV x₁ | Inl g = BV (BVHoleCast g x₁)
  progress (TACast wt (TCHole1 {b})) | BV x₁ | Inr x = abort (x GBase)
  progress (TACast wt (TCHole1 {⦇·⦈})) | BV x₁ | Inr x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCHole1 {τ1 ==> τ2})) | BV x₁ | Inr x
    with typ-dec  (τ1 ==> τ2) (⦇·⦈ ==> ⦇·⦈)
  progress (TACast wt (TCHole1 {.⦇·⦈ ==> .⦇·⦈})) | BV x₂ | Inr x₁ | Inl refl = BV (BVHoleCast GHole x₂)
  progress (TACast wt (TCHole1 {τ1 ==> τ2})) | BV x₂ | Inr x₁ | Inr x = S (_ , Step FHOuter (ITGround (MGArr x)) FHOuter)
  progress (TACast wt (TCHole1 {τ1 ⊗ τ2})) | BV x₁ | Inr x
    with typ-dec  (τ1 ⊗ τ2) (⦇·⦈ ⊗ ⦇·⦈)
  progress (TACast wt (TCHole1 {_ ⊗ _})) | BV x₁ | Inr x | Inl refl = BV (BVHoleCast GProd x₁)
  progress (TACast wt (TCHole1 {_ ⊗ _})) | BV x₁ | Inr x | Inr h    = S (_ , Step FHOuter (ITGround (MGProd h)) FHOuter)
    -- if right is hole
  progress {τ = τ} (TACast wt TCHole2) | BV x
    with canonical-boxed-forms-hole wt x
  progress {τ = τ} (TACast wt TCHole2) | BV x | d' , τ' , refl , gnd , wt'
    with typ-dec τ τ'
  progress (TACast wt TCHole2) | BV x₁ | d' , τ , refl , gnd , wt' | Inl refl = S (_  , Step FHOuter (ITCastSucceed gnd) FHOuter)
  progress {τ = τ} (TACast wt TCHole2) | BV x₁ | _ , _ , refl , _ , _ | Inr _
    with ground-decidable τ
  progress (TACast wt TCHole2) | BV x₂ | _ , _ , refl , gnd , _ | Inr x₁ | Inl x = S(_ , Step FHOuter (ITCastFail gnd x (flip x₁)) FHOuter)
  progress (TACast wt TCHole2) | BV x₂ | _ , _ , refl , _ , _ | Inr x₁ | Inr x
    with notground x
  progress (TACast wt TCHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr _ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt TCHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr h | Inr (Inl (_ , _ , refl)) =
    S (_ , Step FHOuter (ITExpand (MGArr (ground-arr-not-hole h))) FHOuter)
  progress (TACast wt TCHole2) | BV x₃ | _ , _ , refl , _ , _ | Inr _ | Inr h | Inr (Inr (_ , _ , refl)) =
    S (_ , Step FHOuter (ITExpand (MGProd (ground-prod-not-hole h))) FHOuter)
    -- if both arrows
  progress (TACast wt (TCArr {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | BV x
    with typ-dec (τ1 ==> τ2) (τ1' ==> τ2')
  progress (TACast wt (TCArr c1 c2)) | BV x₁ | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCArr c1 c2)) | BV x₁ | Inr x = BV (BVArrCast x x₁)
  progress (TACast wt (TCProd {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | BV x
    with typ-dec (τ1 ⊗ τ2) (τ1' ⊗ τ2')
  progress (TACast wt (TCProd c1 c2)) | BV x | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCProd c1 c2)) | BV x | Inr x₁   = BV (BVProdCast x₁ x)

   -- failed casts
  progress (TAFailedCast wt y z w)
    with progress wt
  progress (TAFailedCast wt y z w) | S (d' , Step x a q) = S (_ , Step (FHFailedCast x) a (FHFailedCast q))
  progress (TAFailedCast wt y z w) | I x = I (IFailedCast (FIndet x) y z w)
  progress (TAFailedCast wt y z w) | BV x = I (IFailedCast (FBoxedVal x) y z w)
