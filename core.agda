open import Nat
open import Prelude
open import List
open import contexts

module core where
  -- types
  data typ : Set where
    b     : typ
    ⦇·⦈    : typ
    _==>_ : typ → typ → typ
    _⊗_   : typ → typ → typ

  -- arrow type constructors bind very tightly
  infixr 25  _==>_
  infixr 25  _⊗_


  -- we use natural numbers as names throughout the development. here we
  -- provide some aliases to that the definitions below are more readable
  -- about what's being named, even though the underlying implementations
  -- are the same and there's no abstraction protecting you from breaking
  -- invariants.

  -- written `x` in math
  varname : Set
  varname = Nat

  -- written `u` in math
  holename : Set
  holename = Nat

  -- written `a` in math
  livelitname : Set
  livelitname = Nat

  -- "external expressions", or the middle layer of expressions. presented
  -- first because of the dependence structure below.
  data eexp : Set where
    c       : eexp
    _·:_    : eexp → typ → eexp
    X       : varname → eexp
    ·λ      : varname → eexp → eexp
    ·λ_[_]_ : varname → typ → eexp → eexp
    ⦇⦈[_]   : holename → eexp
    ⦇⌜_⌟⦈[_] : eexp → holename → eexp
    _∘_     : eexp → eexp → eexp
    ⟨_,_⟩   : eexp → eexp → eexp
    fst     : eexp → eexp
    snd     : eexp → eexp

  -- the type of type contexts, i.e. Γs in the judegments below
  tctx : Set
  tctx = typ ctx

  mutual
    -- identity substitution, substitition environments
    data env : Set where
      Id : (Γ : tctx) → env
      Subst : (d : iexp) → (y : varname) → env → env

    -- internal expressions, the bottom most layer of expresions. these are
    -- what the elaboration phase targets and the expressions on which
    -- evaluation is given.
    data iexp : Set where
      c         : iexp
      X         : varname → iexp
      ·λ_[_]_   : varname → typ → iexp → iexp
      ⦇⦈⟨_⟩     : (holename × env) → iexp
      ⦇⌜_⌟⦈⟨_⟩    : iexp → (holename × env) → iexp
      _∘_       : iexp → iexp → iexp
      _⟨_⇒_⟩    : iexp → typ → typ → iexp
      _⟨_⇒⦇⦈⇏_⟩ : iexp → typ → typ → iexp
      ⟨_,_⟩   : iexp → iexp → iexp
      fst     : iexp → iexp
      snd     : iexp → iexp

  -- convenient notation for chaining together two agreeable casts
  _⟨_⇒_⇒_⟩ : iexp → typ → typ → typ → iexp
  d ⟨ τ1 ⇒ τ2 ⇒ τ3 ⟩ = d ⟨ τ1 ⇒ τ2 ⟩ ⟨ τ2 ⇒ τ3 ⟩

  record livelitdef : Set where
    field
      expand : iexp
      model-type : typ
      expansion-type : typ

  -- unexpanded expressions, the outermost layer of expressions: a langauge
  -- exactly like eexp, but also with livelits
  mutual
    data uexp : Set where
      c       : uexp
      _·:_    : uexp → typ → uexp
      X       : varname → uexp
      ·λ      : varname → uexp → uexp
      ·λ_[_]_ : varname → typ → uexp → uexp
      ⦇⦈[_]   : holename → uexp
      ⦇⌜_⌟⦈[_]  : uexp → holename → uexp
      _∘_     : uexp → uexp → uexp
      ⟨_,_⟩   : uexp → uexp → uexp
      fst     : uexp → uexp
      snd     : uexp → uexp
      -- new forms below
      ＄_⟨_⁏_⟩[_] : (a : livelitname) → (d : iexp) → (ϕᵢ : List splice) → (u : holename) → uexp

    splice : Set
    splice = typ × uexp


  -- type consistency
  data _~_ : (t1 t2 : typ) → Set where
    TCRefl  : {τ : typ} → τ ~ τ
    TCHole1 : {τ : typ} → τ ~ ⦇·⦈
    TCHole2 : {τ : typ} → ⦇·⦈ ~ τ
    TCArr   : {τ1 τ2 τ1' τ2' : typ} →
               τ1 ~ τ1' →
               τ2 ~ τ2' →
               τ1 ==> τ2 ~ τ1' ==> τ2'
    TCProd  : {τ1 τ2 τ1' τ2' : typ} →
               τ1 ~ τ1' →
               τ2 ~ τ2' →
               (τ1 ⊗ τ2) ~ (τ1' ⊗ τ2')

  -- type inconsistency
  data _~̸_ : (τ1 τ2 : typ) → Set where
    ICBaseArr1 : {τ1 τ2 : typ} → b ~̸ τ1 ==> τ2
    ICBaseArr2 : {τ1 τ2 : typ} → τ1 ==> τ2 ~̸ b
    ICArr1 : {τ1 τ2 τ3 τ4 : typ} →
               τ1 ~̸ τ3 →
               τ1 ==> τ2 ~̸ τ3 ==> τ4
    ICArr2 : {τ1 τ2 τ3 τ4 : typ} →
               τ2 ~̸ τ4 →
               τ1 ==> τ2 ~̸ τ3 ==> τ4
    ICBaseProd1 : {τ1 τ2 : typ} → b ~̸ τ1 ⊗ τ2
    ICBaseProd2 : {τ1 τ2 : typ} → τ1 ⊗ τ2 ~̸ b
    ICProdArr1 : {τ1 τ2 τ3 τ4 : typ} →
                τ1 ==> τ2 ~̸ τ3 ⊗ τ4
    ICProdArr2 : {τ1 τ2 τ3 τ4 : typ} →
                τ1 ⊗ τ2 ~̸ τ3 ==> τ4
    ICProd1 : {τ1 τ2 τ3 τ4 : typ} →
               τ1 ~̸ τ3 →
               τ1 ⊗ τ2 ~̸ τ3 ⊗ τ4
    ICProd2 : {τ1 τ2 τ3 τ4 : typ} →
               τ2 ~̸ τ4 →
               τ1 ⊗ τ2 ~̸ τ3 ⊗ τ4

  --- matching for arrows
  data _▸arr_ : typ → typ → Set where
    MAHole : ⦇·⦈ ▸arr ⦇·⦈ ==> ⦇·⦈
    MAArr  : {τ1 τ2 : typ} → τ1 ==> τ2 ▸arr τ1 ==> τ2

  -- matching for products
  data _▸prod_ : typ → typ → Set where
    MPHole : ⦇·⦈ ▸prod ⦇·⦈ ⊗ ⦇·⦈
    MPProd  : {τ1 τ2 : typ} → τ1 ⊗ τ2 ▸prod τ1 ⊗ τ2

  -- the type of hole contexts, i.e. Δs in the judgements
  hctx : Set
  hctx = (typ ctx × typ) ctx

  -- notation for a triple to match the CMTT syntax
  _::_[_] : holename → typ → tctx → (holename × (tctx × typ))
  u :: τ [ Γ ] = u , (Γ , τ)

  -- the hole name u does not appear in the term e
  data hole-name-new : (e : eexp) (u : holename) → Set where
    HNConst : ∀{u} → hole-name-new c u
    HNAsc : ∀{e τ u} →
            hole-name-new e u →
            hole-name-new (e ·: τ) u
    HNVar : ∀{x u} → hole-name-new (X x) u
    HNLam1 : ∀{x e u} →
             hole-name-new e u →
             hole-name-new (·λ x e) u
    HNLam2 : ∀{x e u τ} →
             hole-name-new e u →
             hole-name-new (·λ x [ τ ] e) u
    HNHole : ∀{u u'} →
             u' ≠ u →
             hole-name-new (⦇⦈[ u' ]) u
    HNNEHole : ∀{u u' e} →
               u' ≠ u →
               hole-name-new e u →
               hole-name-new (⦇⌜ e ⌟⦈[ u' ]) u
    HNAp : ∀{ u e1 e2 } →
           hole-name-new e1 u →
           hole-name-new e2 u →
           hole-name-new (e1 ∘ e2) u
    HNFst  : ∀{ u e } →
           hole-name-new e u →
           hole-name-new (fst e) u
    HNSnd  : ∀{ u e } →
           hole-name-new e u →
           hole-name-new (snd e) u
    HNPair : ∀{ u e1 e2 } →
           hole-name-new e1 u →
           hole-name-new e2 u →
           hole-name-new ⟨ e1 , e2 ⟩ u

  -- two terms that do not share any hole names
  data holes-disjoint : (e1 : eexp) → (e2 : eexp) → Set where
    HDConst : ∀{e} → holes-disjoint c e
    HDAsc : ∀{e1 e2 τ} → holes-disjoint e1 e2 → holes-disjoint (e1 ·: τ) e2
    HDVar : ∀{x e} → holes-disjoint (X x) e
    HDLam1 : ∀{x e1 e2} → holes-disjoint e1 e2 → holes-disjoint (·λ x e1) e2
    HDLam2 : ∀{x e1 e2 τ} → holes-disjoint e1 e2 → holes-disjoint (·λ x [ τ ] e1) e2
    HDHole : ∀{u e2} → hole-name-new e2 u → holes-disjoint (⦇⦈[ u ]) e2
    HDNEHole : ∀{u e1 e2} → hole-name-new e2 u → holes-disjoint e1 e2 → holes-disjoint (⦇⌜ e1 ⌟⦈[ u ]) e2
    HDAp :  ∀{e1 e2 e3} → holes-disjoint e1 e3 → holes-disjoint e2 e3 → holes-disjoint (e1 ∘ e2) e3
    HDFst  : ∀{e1 e2} → holes-disjoint e1 e2 → holes-disjoint (fst e1) e2
    HDSnd  : ∀{e1 e2} → holes-disjoint e1 e2 → holes-disjoint (snd e1) e2
    HDPair : ∀{e1 e2 e3} → holes-disjoint e1 e3 → holes-disjoint e2 e3 → holes-disjoint ⟨ e1 , e2 ⟩ e3

  -- bidirectional type checking judgements for eexp
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : tctx) (e : eexp) (τ : typ) → Set where
      SConst  : {Γ : tctx} → Γ ⊢ c => b
      SAsc    : {Γ : tctx} {e : eexp} {τ : typ} →
                 Γ ⊢ e <= τ →
                 Γ ⊢ (e ·: τ) => τ
      SVar    : {Γ : tctx} {τ : typ} {x : varname} →
                 (x , τ) ∈ Γ →
                 Γ ⊢ X x => τ
      SAp     : {Γ : tctx} {e1 e2 : eexp} {τ τ1 τ2 : typ} →
                 holes-disjoint e1 e2 →
                 Γ ⊢ e1 => τ1 →
                 τ1 ▸arr τ2 ==> τ →
                 Γ ⊢ e2 <= τ2 →
                 Γ ⊢ (e1 ∘ e2) => τ
      SEHole  : {Γ : tctx} {u : holename} → Γ ⊢ ⦇⦈[ u ] => ⦇·⦈
      SNEHole : {Γ : tctx} {e : eexp} {τ : typ} {u : holename} →
                 hole-name-new e u →
                 Γ ⊢ e => τ →
                 Γ ⊢ ⦇⌜ e ⌟⦈[ u ] => ⦇·⦈
      SLam    : {Γ : tctx} {e : eexp} {τ1 τ2 : typ} {x : varname} →
                 x # Γ →
                 (Γ ,, (x , τ1)) ⊢ e => τ2 →
                 Γ ⊢ ·λ x [ τ1 ] e => τ1 ==> τ2
      SFst    : ∀{ e τ τ1 τ2 Γ} →
                Γ ⊢ e => τ →
                τ ▸prod τ1 ⊗ τ2 →
                Γ ⊢ fst e => τ1
      SSnd    : ∀{ e τ τ1 τ2 Γ} →
                Γ ⊢ e => τ →
                τ ▸prod τ1 ⊗ τ2 →
                Γ ⊢ snd e => τ2
      SPair   : ∀{ e1 e2 τ1 τ2 Γ} →
                holes-disjoint e1 e2 →
                Γ ⊢ e1 => τ1 →
                Γ ⊢ e2 => τ2 →
                Γ ⊢ ⟨ e1 , e2 ⟩ => τ1 ⊗ τ2

    -- analysis
    data _⊢_<=_ : (Γ : tctx) (e : eexp) (τ : typ) → Set where
      ASubsume : {Γ : tctx} {e : eexp} {τ τ' : typ} →
                 Γ ⊢ e => τ' →
                 τ ~ τ' →
                 Γ ⊢ e <= τ
      ALam : {Γ : tctx} {e : eexp} {τ τ1 τ2 : typ} {x : varname} →
                 x # Γ →
                 τ ▸arr τ1 ==> τ2 →
                 (Γ ,, (x , τ1)) ⊢ e <= τ2 →
                 Γ ⊢ (·λ x e) <= τ

  -- those types without holes
  data _tcomplete : typ → Set where
    TCBase : b tcomplete
    TCArr : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ==> τ2) tcomplete
    TCProd : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ⊗ τ2) tcomplete

  -- those external expressions without holes
  data _ecomplete : eexp → Set where
    ECConst : c ecomplete
    ECAsc : ∀{τ e} → τ tcomplete → e ecomplete → (e ·: τ) ecomplete
    ECVar : ∀{x} → (X x) ecomplete
    ECLam1 : ∀{x e} → e ecomplete → (·λ x e) ecomplete
    ECLam2 : ∀{x e τ} → e ecomplete → τ tcomplete → (·λ x [ τ ] e) ecomplete
    ECAp : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
    ECFst : ∀{e} → e ecomplete → (fst e) ecomplete
    ECSnd : ∀{e} → e ecomplete → (snd e) ecomplete
    ECPair : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → ⟨ e1 , e2 ⟩ ecomplete

  -- those internal expressions without holes
  data _dcomplete : iexp → Set where
    DCVar : ∀{x} → (X x) dcomplete
    DCConst : c dcomplete
    DCLam : ∀{x τ d} → d dcomplete → τ tcomplete → (·λ x [ τ ] d) dcomplete
    DCAp : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → (d1 ∘ d2) dcomplete
    DCCast : ∀{d τ1 τ2} → d dcomplete → τ1 tcomplete → τ2 tcomplete → (d ⟨ τ1 ⇒ τ2 ⟩) dcomplete
    DCFst : ∀{d} → d dcomplete → (fst d) dcomplete
    DCSnd : ∀{d} → d dcomplete → (snd d) dcomplete
    DCPair : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → ⟨ d1 , d2 ⟩ dcomplete


  -- contexts that only produce complete types
  _gcomplete : tctx → Set
  Γ gcomplete = (x : varname) (τ : typ) → (x , τ) ∈ Γ → τ tcomplete

  -- those internal expressions where every cast is the identity cast and
  -- there are no failed casts
  data cast-id : iexp → Set where
    CIConst  : cast-id c
    CIVar    : ∀{x} → cast-id (X x)
    CILam    : ∀{x τ d} → cast-id d → cast-id (·λ x [ τ ] d)
    CIHole   : ∀{u} → cast-id (⦇⦈⟨ u ⟩)
    CINEHole : ∀{d u} → cast-id d → cast-id (⦇⌜ d ⌟⦈⟨ u ⟩)
    CIAp     : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id (d1 ∘ d2)
    CICast   : ∀{d τ} → cast-id d → cast-id (d ⟨ τ ⇒ τ ⟩)
    CIFst    : ∀{d} → cast-id d → cast-id (fst d)
    CISnd    : ∀{d} → cast-id d → cast-id (snd d)
    CIPair   : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id ⟨ d1 , d2 ⟩

  -- expansion
  mutual
    -- synthesis
    data _⊢_⇒_~>_⊣_ : (Γ : tctx) (e : eexp) (τ : typ) (d : iexp) (Δ : hctx) → Set where
      ESConst : ∀{Γ} → Γ ⊢ c ⇒ b ~> c ⊣ ∅
      ESVar   : ∀{Γ x τ} → (x , τ) ∈ Γ →
                         Γ ⊢ X x ⇒ τ ~> X x ⊣ ∅
      ESLam   : ∀{Γ x τ1 τ2 e d Δ } →
                     (x # Γ) →
                     (Γ ,, (x , τ1)) ⊢ e ⇒ τ2 ~> d ⊣ Δ →
                      Γ ⊢ ·λ x [ τ1 ] e ⇒ (τ1 ==> τ2) ~> ·λ x [ τ1 ] d ⊣ Δ
      ESAp : ∀{Γ e1 τ τ1 τ1' τ2 τ2' d1 Δ1 e2 d2 Δ2 } →
              holes-disjoint e1 e2 →
              Δ1 ## Δ2 →
              Γ ⊢ e1 => τ1 →
              τ1 ▸arr τ2 ==> τ →
              Γ ⊢ e1 ⇐ (τ2 ==> τ) ~> d1 :: τ1' ⊣ Δ1 →
              Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' ⊣ Δ2 →
              Γ ⊢ e1 ∘ e2 ⇒ τ ~> (d1 ⟨ τ1' ⇒ τ2 ==> τ ⟩) ∘ (d2 ⟨ τ2' ⇒ τ2 ⟩) ⊣ (Δ1 ∪ Δ2)
      ESEHole : ∀{ Γ u } →
                Γ ⊢ ⦇⦈[ u ] ⇒ ⦇·⦈ ~> ⦇⦈⟨ u , Id Γ ⟩ ⊣  ■ (u :: ⦇·⦈ [ Γ ])
      ESNEHole : ∀{ Γ e τ d u Δ } →
                 Δ ## (■ (u , Γ , ⦇·⦈)) →
                 Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                 Γ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇒ ⦇·⦈ ~> ⦇⌜ d ⌟⦈⟨ u , Id Γ  ⟩ ⊣ (Δ ,, u :: ⦇·⦈ [ Γ ])
      ESAsc : ∀ {Γ e τ d τ' Δ} →
                 Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                 Γ ⊢ (e ·: τ) ⇒ τ ~> d ⟨ τ' ⇒ τ ⟩ ⊣ Δ
      ESFst  : ∀{Γ e τ τ' d τ1 τ2 Δ} →
                 Γ ⊢ e => τ →
                 τ ▸prod τ1 ⊗ τ2 →
                 Γ ⊢ e ⇐ τ1 ⊗ τ2 ~> d :: τ' ⊣ Δ →
                 Γ ⊢ fst e ⇒ τ1 ~> fst (d ⟨ τ' ⇒ τ1 ⊗ τ2 ⟩) ⊣ Δ
      ESSnd  : ∀{Γ e τ τ' d τ1 τ2 Δ} →
                 Γ ⊢ e => τ →
                 τ ▸prod τ1 ⊗ τ2 →
                 Γ ⊢ e ⇐ τ1 ⊗ τ2 ~> d :: τ' ⊣ Δ →
                 Γ ⊢ snd e ⇒ τ2 ~> snd (d ⟨ τ' ⇒ τ1 ⊗ τ2 ⟩) ⊣ Δ
      ESPair : ∀{Γ e1 τ1 d1 Δ1 e2 τ2 d2 Δ2} →
                 holes-disjoint e1 e2 →
                 Δ1 ## Δ2 →
                 Γ ⊢ e1 ⇒ τ1 ~> d1 ⊣ Δ1 →
                 Γ ⊢ e2 ⇒ τ2 ~> d2 ⊣ Δ2 →
                 Γ ⊢ ⟨ e1 , e2 ⟩ ⇒ τ1 ⊗ τ2 ~> ⟨ d1 , d2 ⟩ ⊣ (Δ1 ∪ Δ2)

    -- analysis
    data _⊢_⇐_~>_::_⊣_ : (Γ : tctx) (e : eexp) (τ : typ) (d : iexp) (τ' : typ) (Δ : hctx) → Set where
      EALam : ∀{Γ x τ τ1 τ2 e d τ2' Δ } →
              (x # Γ) →
              τ ▸arr τ1 ==> τ2 →
              (Γ ,, (x , τ1)) ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
              Γ ⊢ ·λ x e ⇐ τ ~> ·λ x [ τ1 ] d :: τ1 ==> τ2' ⊣ Δ
      EASubsume : ∀{e Γ τ' d Δ τ} →
                  ((u : holename) → e ≠ ⦇⦈[ u ]) →
                  ((e' : eexp) (u : holename) → e ≠ ⦇⌜ e' ⌟⦈[ u ]) →
                  Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                  τ ~ τ' →
                  Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
      EAEHole : ∀{ Γ u τ  } →
                Γ ⊢ ⦇⦈[ u ] ⇐ τ ~> ⦇⦈⟨ u , Id Γ  ⟩ :: τ ⊣ ■ (u :: τ [ Γ ])
      EANEHole : ∀{ Γ e u τ d τ' Δ  } →
                 Δ ## (■ (u , Γ , τ)) →
                 Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                 Γ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇐ τ ~> ⦇⌜ d ⌟⦈⟨ u , Id Γ  ⟩ :: τ ⊣ (Δ ,, u :: τ [ Γ ])

  -- ground types
  data _ground : (τ : typ) → Set where
    GBase : b ground
    GHole : ⦇·⦈ ==> ⦇·⦈ ground
    GProd : ⦇·⦈ ⊗ ⦇·⦈ ground

  mutual
    -- substitution typing
    data _,_⊢_:s:_ : hctx → tctx → env → tctx → Set where
      STAId : ∀{Γ Γ' Δ} →
                  ((x : varname) (τ : typ) → (x , τ) ∈ Γ' → (x , τ) ∈ Γ) →
                  Δ , Γ ⊢ Id Γ' :s: Γ'
      STASubst : ∀{Γ Δ σ y Γ' d τ } →
               Δ , Γ ,, (y , τ) ⊢ σ :s: Γ' →
               Δ , Γ ⊢ d :: τ →
               Δ , Γ ⊢ Subst d y σ :s: Γ'

    -- type assignment
    data _,_⊢_::_ : (Δ : hctx) (Γ : tctx) (d : iexp) (τ : typ) → Set where
      TAConst : ∀{Δ Γ} → Δ , Γ ⊢ c :: b
      TAVar : ∀{Δ Γ x τ} → (x , τ) ∈ Γ → Δ , Γ ⊢ X x :: τ
      TALam : ∀{ Δ Γ x τ1 d τ2} →
              x # Γ →
              Δ , (Γ ,, (x , τ1)) ⊢ d :: τ2 →
              Δ , Γ ⊢ ·λ x [ τ1 ] d :: (τ1 ==> τ2)
      TAAp : ∀{ Δ Γ d1 d2 τ1 τ} →
             Δ , Γ ⊢ d1 :: τ1 ==> τ →
             Δ , Γ ⊢ d2 :: τ1 →
             Δ , Γ ⊢ d1 ∘ d2 :: τ
      TAEHole : ∀{ Δ Γ σ u Γ' τ} →
                (u , (Γ' , τ)) ∈ Δ →
                Δ , Γ ⊢ σ :s: Γ' →
                Δ , Γ ⊢ ⦇⦈⟨ u , σ ⟩ :: τ
      TANEHole : ∀ { Δ Γ d τ' Γ' u σ τ } →
                 (u , (Γ' , τ)) ∈ Δ →
                 Δ , Γ ⊢ d :: τ' →
                 Δ , Γ ⊢ σ :s: Γ' →
                 Δ , Γ ⊢ ⦇⌜ d ⌟⦈⟨ u , σ ⟩ :: τ
      TACast : ∀{ Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 →
             τ1 ~ τ2 →
             Δ , Γ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2
      TAFailedCast : ∀{Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 →
             τ1 ground →
             τ2 ground →
             τ1 ≠ τ2 →
             Δ , Γ ⊢ d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩ :: τ2
      TAFst : ∀{Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 ⊗ τ2 →
             Δ , Γ ⊢ fst d :: τ1
      TASnd : ∀{Δ Γ d τ1 τ2} →
             Δ , Γ ⊢ d :: τ1 ⊗ τ2 →
             Δ , Γ ⊢ snd d :: τ2
      TAPair : ∀{Δ Γ d1 d2 τ1 τ2} →
             Δ , Γ ⊢ d1 :: τ1 →
             Δ , Γ ⊢ d2 :: τ2 →
             Δ , Γ ⊢ ⟨ d1 , d2 ⟩ :: τ1 ⊗ τ2

  -- substitution
  [_/_]_ : iexp → varname → iexp → iexp
  [ d / y ] c = c
  [ d / y ] X x
    with natEQ x y
  [ d / y ] X .y | Inl refl = d
  [ d / y ] X x  | Inr neq = X x
  [ d / y ] (·λ x [ x₁ ] d')
    with natEQ x y
  [ d / y ] (·λ .y [ τ ] d') | Inl refl = ·λ y [ τ ] d'
  [ d / y ] (·λ x [ τ ] d')  | Inr x₁ = ·λ x [ τ ] ( [ d / y ] d')
  [ d / y ] ⦇⦈⟨ u , σ ⟩ = ⦇⦈⟨ u , Subst d y σ ⟩
  [ d / y ] ⦇⌜ d' ⌟⦈⟨ u , σ  ⟩ =  ⦇⌜ [ d / y ] d' ⌟⦈⟨ u , Subst d y σ ⟩
  [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
  [ d / y ] (d' ⟨ τ1 ⇒ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒ τ2 ⟩
  [ d / y ] (d' ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩
  [ d / y ] ⟨ d1 , d2 ⟩ = ⟨ [ d / y ] d1 , [ d / y ] d2 ⟩
  [ d / y ] (fst d') = fst ([ d / y ] d')
  [ d / y ] (snd d') = snd ([ d / y ] d')

  -- applying an environment to an expression
  apply-env : env → iexp → iexp
  apply-env (Id Γ) d = d
  apply-env (Subst d y σ) d' = [ d / y ] ( apply-env σ d')

  -- values
  data _val : (d : iexp) → Set where
    VConst : c val
    VLam   : ∀{x τ d} → (·λ x [ τ ] d) val
    VPair  : ∀{d1 d2} → d1 val → d2 val → ⟨ d1 , d2 ⟩ val

  -- boxed values
  data _boxedval : (d : iexp) → Set where
    BVVal : ∀{d} → d val → d boxedval
    BVPair : ∀{d1 d2} → d1 boxedval → d2 boxedval → ⟨ d1 , d2 ⟩ boxedval
    BVArrCast : ∀{ d τ1 τ2 τ3 τ4 } →
                τ1 ==> τ2 ≠ τ3 ==> τ4 →
                d boxedval →
                d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ boxedval
    BVProdCast : ∀{ d τ1 τ2 τ3 τ4 } →
                τ1 ⊗ τ2 ≠ τ3 ⊗ τ4 →
                d boxedval →
                d ⟨ (τ1 ⊗ τ2) ⇒ (τ3 ⊗ τ4) ⟩ boxedval
    BVHoleCast : ∀{ τ d } → τ ground → d boxedval → d ⟨ τ ⇒ ⦇·⦈ ⟩ boxedval

  mutual
    -- indeterminate forms
    data _indet : (d : iexp) → Set where
      IEHole : ∀{u σ} → ⦇⦈⟨ u , σ ⟩ indet
      INEHole : ∀{d u σ} → d final → ⦇⌜ d ⌟⦈⟨ u , σ ⟩ indet
      IAp : ∀{d1 d2} → ((τ1 τ2 τ3 τ4 : typ) (d1' : iexp) →
                       d1 ≠ (d1' ⟨(τ1 ==> τ2) ⇒ (τ3 ==> τ4)⟩)) →
                       d1 indet →
                       d2 final →
                       (d1 ∘ d2) indet
      IFst   : ∀{d} →
               d indet →
               (∀{d1 d2} → d ≠ ⟨ d1 , d2 ⟩) →
               (∀{d' τ1 τ2 τ3 τ4} → d ≠ (d' ⟨ τ1 ⊗ τ2 ⇒ τ3 ⊗ τ4 ⟩)) →
               (fst d) indet
      ISnd   : ∀{d} →
               d indet →
               (∀{d1 d2} → d ≠ ⟨ d1 , d2 ⟩) →
               (∀{d' τ1 τ2 τ3 τ4} → d ≠ (d' ⟨ τ1 ⊗ τ2 ⇒ τ3 ⊗ τ4 ⟩)) →
               (snd d) indet
      IPair1 : ∀{d1 d2} →
               d1 indet →
               d2 final →
               ⟨ d1 , d2 ⟩ indet
      IPair2 : ∀{d1 d2} →
               d1 final →
               d2 indet →
               ⟨ d1 , d2 ⟩ indet
      ICastArr : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ==> τ2 ≠ τ3 ==> τ4 →
                 d indet →
                 d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ indet
      ICastProd : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ⊗ τ2 ≠ τ3 ⊗ τ4 →
                 d indet →
                 d ⟨ (τ1 ⊗ τ2) ⇒ (τ3 ⊗ τ4) ⟩ indet
      ICastGroundHole : ∀{ τ d } →
                        τ ground →
                        d indet →
                        d ⟨ τ ⇒  ⦇·⦈ ⟩ indet
      ICastHoleGround : ∀ { d τ } →
                        ((d' : iexp) (τ' : typ) → d ≠ (d' ⟨ τ' ⇒ ⦇·⦈ ⟩)) →
                        d indet →
                        τ ground →
                        d ⟨ ⦇·⦈ ⇒ τ ⟩ indet
      IFailedCast : ∀{ d τ1 τ2 } →
                    d final →
                    τ1 ground →
                    τ2 ground →
                    τ1 ≠ τ2 →
                    d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩ indet

    -- final expressions
    data _final : (d : iexp) → Set where
      FBoxedVal : ∀{d} → d boxedval → d final
      FIndet    : ∀{d} → d indet    → d final


  -- contextual dynamics

  -- evaluation contexts
  data ectx : Set where
    ⊙ : ectx
    _∘₁_ : ectx → iexp → ectx
    _∘₂_ : iexp → ectx → ectx
    ⦇⌜_⌟⦈⟨_⟩ : ectx → (holename × env ) → ectx
    fst·_ : ectx → ectx
    snd·_ : ectx → ectx
    ⟨_,_⟩₁ : ectx → iexp → ectx
    ⟨_,_⟩₂ : iexp → ectx → ectx
    _⟨_⇒_⟩ : ectx → typ → typ → ectx
    _⟨_⇒⦇·⦈⇏_⟩ : ectx → typ → typ → ectx

  -- note: this judgement is redundant: in the absence of the premises in
  -- the red brackets, all syntactically well formed ectxs are valid. with
  -- finality premises, that's not true, and that would propagate through
  -- additions to the calculus. so we leave it here for clarity but note
  -- that, as written, in any use case its either trival to prove or
  -- provides no additional information

   --ε is an evaluation context
  data _evalctx : (ε : ectx) → Set where
    ECDot : ⊙ evalctx
    ECAp1 : ∀{d ε} →
            ε evalctx →
            (ε ∘₁ d) evalctx
    ECAp2 : ∀{d ε} →
            -- d final → -- red brackets
            ε evalctx →
            (d ∘₂ ε) evalctx
    ECNEHole : ∀{ε u σ} →
               ε evalctx →
               ⦇⌜ ε ⌟⦈⟨ u , σ ⟩ evalctx
    ECFst   : ∀{ε} →
              (fst· ε) evalctx
    ECSnd   : ∀{ε} →
              (snd· ε) evalctx
    ECPair1 : ∀{d ε} →
              ε evalctx →
              ⟨ ε , d ⟩₁ evalctx
    ECPair2 : ∀{d ε} →
              -- d final → -- red brackets
              ε evalctx →
              ⟨ d , ε ⟩₂ evalctx
    ECCast : ∀{ ε τ1 τ2} →
             ε evalctx →
             (ε ⟨ τ1 ⇒ τ2 ⟩) evalctx
    ECFailedCast : ∀{ ε τ1 τ2 } →
                   ε evalctx →
                   ε ⟨ τ1 ⇒⦇·⦈⇏ τ2 ⟩ evalctx

  -- d is the result of filling the hole in ε with d'
  data _==_⟦_⟧ : (d : iexp) (ε : ectx) (d' : iexp) → Set where
    FHOuter : ∀{d} → d == ⊙ ⟦ d ⟧
    FHAp1 : ∀{d1 d1' d2 ε} →
           d1 == ε ⟦ d1' ⟧ →
           (d1 ∘ d2) == (ε ∘₁ d2) ⟦ d1' ⟧
    FHAp2 : ∀{d1 d2 d2' ε} →
           -- d1 final → -- red brackets
           d2 == ε ⟦ d2' ⟧ →
           (d1 ∘ d2) == (d1 ∘₂ ε) ⟦ d2' ⟧
    FHNEHole : ∀{ d d' ε u σ} →
              d == ε ⟦ d' ⟧ →
              ⦇⌜ d ⌟⦈⟨ (u , σ ) ⟩ ==  ⦇⌜ ε ⌟⦈⟨ (u , σ ) ⟩ ⟦ d' ⟧
    FHFst   : ∀{d d' ε} →
              d == ε ⟦ d' ⟧ →
              fst d == (fst· ε) ⟦ d' ⟧
    FHSnd   : ∀{d d' ε} →
              d == ε ⟦ d' ⟧ →
              snd d == (snd· ε) ⟦ d' ⟧
    FHPair1 : ∀{d1 d1' d2 ε} →
              d1 == ε ⟦ d1' ⟧ →
              ⟨ d1 , d2 ⟩ == ⟨ ε , d2 ⟩₁ ⟦ d1' ⟧
    FHPair2 : ∀{d1 d2 d2' ε} →
              d2 == ε ⟦ d2' ⟧ →
              ⟨ d1 , d2 ⟩ == ⟨ d1 , ε ⟩₂ ⟦ d2' ⟧
    FHCast : ∀{ d d' ε τ1 τ2 } →
            d == ε ⟦ d' ⟧ →
            d ⟨ τ1 ⇒ τ2 ⟩ == ε ⟨ τ1 ⇒ τ2 ⟩ ⟦ d' ⟧
    FHFailedCast : ∀{ d d' ε τ1 τ2} →
            d == ε ⟦ d' ⟧ →
            (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩) == (ε ⟨ τ1 ⇒⦇·⦈⇏ τ2 ⟩) ⟦ d' ⟧

  -- matched ground types
  data _▸gnd_ : typ → typ → Set where
    MGArr : ∀{τ1 τ2} →
            (τ1 ==> τ2) ≠ (⦇·⦈ ==> ⦇·⦈) →
            (τ1 ==> τ2) ▸gnd (⦇·⦈ ==> ⦇·⦈)
    MGProd : ∀{τ1 τ2} →
            (τ1 ⊗ τ2) ≠ (⦇·⦈ ⊗ ⦇·⦈) →
            (τ1 ⊗ τ2) ▸gnd (⦇·⦈ ⊗ ⦇·⦈)

  -- instruction transition judgement
  data _→>_ : (d d' : iexp) → Set where
    ITLam : ∀{ x τ d1 d2 } →
            -- d2 final → -- red brackets
            ((·λ x [ τ ] d1) ∘ d2) →> ([ d2 / x ] d1)
    ITFst : ∀{d1 d2} →
            -- d1 final → -- red brackets
            -- d2 final → -- red brackets
            fst ⟨ d1 , d2 ⟩ →> d1
    ITSnd : ∀{d1 d2} →
            -- d1 final → -- red brackets
            -- d2 final → -- red brackets
            snd ⟨ d1 , d2 ⟩ →> d2
    ITCastID : ∀{d τ } →
               -- d final → -- red brackets
               (d ⟨ τ ⇒ τ ⟩) →> d
    ITCastSucceed : ∀{d τ } →
                    -- d final → -- red brackets
                    τ ground →
                    (d ⟨ τ ⇒ ⦇·⦈ ⇒ τ ⟩) →> d
    ITCastFail : ∀{ d τ1 τ2} →
                 -- d final → -- red brackets
                 τ1 ground →
                 τ2 ground →
                 τ1 ≠ τ2 →
                 (d ⟨ τ1 ⇒ ⦇·⦈ ⇒ τ2 ⟩) →> (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)
    ITApCast : ∀{d1 d2 τ1 τ2 τ1' τ2' } →
               -- d1 final → -- red brackets
               -- d2 final → -- red brackets
               ((d1 ⟨ (τ1 ==> τ2) ⇒ (τ1' ==> τ2')⟩) ∘ d2) →> ((d1 ∘ (d2 ⟨ τ1' ⇒ τ1 ⟩)) ⟨ τ2 ⇒ τ2' ⟩)
    ITFstCast : ∀{d τ1 τ2 τ1' τ2' } →
               -- d final → -- red brackets
               fst (d ⟨ τ1 ⊗ τ2 ⇒ τ1' ⊗ τ2' ⟩) →> ((fst d) ⟨ τ1 ⇒ τ1' ⟩)
    ITSndCast : ∀{d τ1 τ2 τ1' τ2' } →
               -- d final → -- red brackets
               snd (d ⟨ τ1 ⊗ τ2 ⇒ τ1' ⊗ τ2' ⟩) →> ((snd d) ⟨ τ2 ⇒ τ2' ⟩)
    ITGround : ∀{ d τ τ'} →
               -- d final → -- red brackets
               τ ▸gnd τ' →
               (d ⟨ τ ⇒ ⦇·⦈ ⟩) →> (d ⟨ τ ⇒ τ' ⇒ ⦇·⦈ ⟩)
    ITExpand : ∀{d τ τ' } →
               -- d final → -- red brackets
               τ ▸gnd τ' →
               (d ⟨ ⦇·⦈ ⇒ τ ⟩) →> (d ⟨ ⦇·⦈ ⇒ τ' ⇒ τ ⟩)

  -- single step (in contextual evaluation sense)
  data _↦_ : (d d' : iexp) → Set where
    Step : ∀{ d d0 d' d0' ε} →
           d == ε ⟦ d0 ⟧ →
           d0 →> d0' →
           d' == ε ⟦ d0' ⟧ →
           d ↦ d'

  -- reflexive transitive closure of single steps into multi steps
  data _↦*_ : (d d' : iexp) → Set where
    MSRefl : ∀{d} → d ↦* d
    MSStep : ∀{d d' d''} →
                 d ↦ d' →
                 d' ↦* d'' →
                 d  ↦* d''

  -- freshness
  mutual
    -- ... with respect to a hole context
    data envfresh : varname → env → Set where
      EFId : ∀{x Γ} → x # Γ → envfresh x (Id Γ)
      EFSubst : ∀{x d σ y} → fresh x d
                           → envfresh x σ
                           → x ≠ y
                           → envfresh x (Subst d y σ)

    -- ... for inernal expressions
    data fresh : varname → iexp → Set where
      FConst : ∀{x} → fresh x c
      FVar   : ∀{x y} → x ≠ y → fresh x (X y)
      FLam   : ∀{x y τ d} → x ≠ y → fresh x d → fresh x (·λ y [ τ ] d)
      FHole  : ∀{x u σ} → envfresh x σ → fresh x (⦇⦈⟨ u , σ ⟩)
      FNEHole : ∀{x d u σ} → envfresh x σ → fresh x d → fresh x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      FAp     : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x (d1 ∘ d2)
      FCast   : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒ τ2 ⟩)
      FFailedCast : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)
      FFst  : ∀{x d} → fresh x d → fresh x (fst d)
      FSnd  : ∀{x d} → fresh x d → fresh x (snd d)
      FPair : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x ⟨ d1 , d2 ⟩

  -- ... for external expressions
  data freshe : varname → eexp → Set where
    FRHConst : ∀{x} → freshe x c
    FRHAsc   : ∀{x e τ} → freshe x e → freshe x (e ·: τ)
    FRHVar   : ∀{x y} → x ≠ y → freshe x (X y)
    FRHLam1  : ∀{x y e} → x ≠ y → freshe x e → freshe x (·λ y e)
    FRHLam2  : ∀{x τ e y} → x ≠ y → freshe x e → freshe x (·λ y [ τ ] e)
    FRHEHole : ∀{x u} → freshe x (⦇⦈[ u ])
    FRHNEHole : ∀{x u e} → freshe x e → freshe x (⦇⌜ e ⌟⦈[ u ])
    FRHAp : ∀{x e1 e2} → freshe x e1 → freshe x e2 → freshe x (e1 ∘ e2)
    FRHFst  : ∀{x e} → freshe x e → freshe x (fst e)
    FRHSnd  : ∀{x e} → freshe x e → freshe x (snd e)
    FRHPair : ∀{x e1 e2} → freshe x e1 → freshe x e2 → freshe x ⟨ e1 , e2 ⟩

  -- with respect to all bindings in a context
  freshΓ : {A : Set} → (Γ : A ctx) → (e : eexp) → Set
  freshΓ {A} Γ e = (x : varname) → dom Γ x → freshe x e

  -- x is not used in a binding site in d
  mutual
    data unbound-in-σ : varname → env → Set where
      UBσId : ∀{x Γ} → unbound-in-σ x (Id Γ)
      UBσSubst : ∀{x d y σ} → unbound-in x d
                            → unbound-in-σ x σ
                            → x ≠ y
                            → unbound-in-σ x (Subst d y σ)

    data unbound-in : (x : varname) (d : iexp) → Set where
      UBConst : ∀{x} → unbound-in x c
      UBVar : ∀{x y} → unbound-in x (X y)
      UBLam2 : ∀{x d y τ} → x ≠ y
                           → unbound-in x d
                           → unbound-in x (·λ_[_]_ y τ d)
      UBHole : ∀{x u σ} → unbound-in-σ x σ
                         → unbound-in x (⦇⦈⟨ u , σ ⟩)
      UBNEHole : ∀{x u σ d }
                  → unbound-in-σ x σ
                  → unbound-in x d
                  → unbound-in x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      UBAp : ∀{ x d1 d2 } →
            unbound-in x d1 →
            unbound-in x d2 →
            unbound-in x (d1 ∘ d2)
      UBCast : ∀{x d τ1 τ2} → unbound-in x d → unbound-in x (d ⟨ τ1 ⇒ τ2 ⟩)
      UBFailedCast : ∀{x d τ1 τ2} → unbound-in x d → unbound-in x (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)
      UBFst  : ∀{x d} → unbound-in x d → unbound-in x (fst d)
      UBSnd  : ∀{x d} → unbound-in x d → unbound-in x (snd d)
      UBPair : ∀{x d1 d2} → unbound-in x d1 → unbound-in x d2 → unbound-in x ⟨ d1 , d2 ⟩

  mutual
    remove-from-free' : varname → eexp → List varname
    remove-from-free' x e = remove-all natEQ (free-vars e) x

    free-vars : (e : eexp) → List varname
    free-vars c = []
    free-vars (e ·: τ) = free-vars e
    free-vars (X x) = x :: []
    free-vars (·λ x e) = remove-from-free' x e
    free-vars (·λ x [ τ ] e) = remove-from-free' x e
    free-vars ⦇⦈[ u ] = []
    free-vars ⦇⌜ e ⌟⦈[ u ] = free-vars e
    free-vars (e₁ ∘ e₂) = free-vars e₁ ++ free-vars e₂
    free-vars ⟨ x , x₁ ⟩ = free-vars x ++ free-vars x₁
    free-vars (fst x) = free-vars x
    free-vars (snd x) = free-vars x

  mutual
    data binders-disjoint-σ : env → iexp → Set where
      BDσId : ∀{Γ d} → binders-disjoint-σ (Id Γ) d
      BDσSubst : ∀{d1 d2 y σ} → binders-disjoint d1 d2
                              → binders-disjoint-σ σ d2
                              → binders-disjoint-σ (Subst d1 y σ) d2

    -- two terms that do not share any binders
    data binders-disjoint : (d1 : iexp) → (d2 : iexp) → Set where
      BDConst : ∀{d} → binders-disjoint c d
      BDVar : ∀{x d} → binders-disjoint (X x) d
      BDLam : ∀{x τ d1 d2} → binders-disjoint d1 d2
                            → unbound-in x d2
                            → binders-disjoint (·λ_[_]_ x τ d1) d2
      BDHole : ∀{u σ d2} → binders-disjoint-σ σ d2
                         → binders-disjoint (⦇⦈⟨ u , σ ⟩) d2
      BDNEHole : ∀{u σ d1 d2} → binders-disjoint-σ σ d2
                              → binders-disjoint d1 d2
                              → binders-disjoint (⦇⌜ d1 ⌟⦈⟨ u , σ ⟩) d2
      BDAp :  ∀{d1 d2 d3} → binders-disjoint d1 d3
                          → binders-disjoint d2 d3
                          → binders-disjoint (d1 ∘ d2) d3
      BDCast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint (d1 ⟨ τ1 ⇒ τ2 ⟩) d2
      BDFailedCast : ∀{d1 d2 τ1 τ2} → binders-disjoint d1 d2 → binders-disjoint (d1 ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩) d2
      BDFst  : ∀{d1 d2} → binders-disjoint d1 d2 → binders-disjoint (fst d1) d2
      BDSnd  : ∀{d1 d2} → binders-disjoint d1 d2 → binders-disjoint (snd d1) d2
      BDPair : ∀{d1 d2 d3} →
               binders-disjoint d1 d3 →
               binders-disjoint d2 d3 →
               binders-disjoint ⟨ d1 , d2 ⟩ d3

  mutual
  -- each term has to be binders unique, and they have to be pairwise
  -- disjoint with the collection of bound vars
    data binders-unique-σ : env → Set where
      BUσId : ∀{Γ} → binders-unique-σ (Id Γ)
      BUσSubst : ∀{d y σ} → binders-unique d
                          → binders-unique-σ σ
                          → binders-disjoint-σ σ d
                          → binders-unique-σ (Subst d y σ)

    -- all the variable names in the term are unique
    data binders-unique : iexp → Set where
      BUHole : binders-unique c
      BUVar : ∀{x} → binders-unique (X x)
      BULam : {x : varname} {τ : typ} {d : iexp} → binders-unique d
                                                → unbound-in x d
                                                → binders-unique (·λ_[_]_ x τ d)
      BUEHole : ∀{u σ} → binders-unique-σ σ
                        → binders-unique (⦇⦈⟨ u , σ ⟩)
      BUNEHole : ∀{u σ d} → binders-unique d
                           → binders-unique-σ σ
                           → binders-unique (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      BUAp : ∀{d1 d2} → binders-unique d1
                       → binders-unique d2
                       → binders-disjoint d1 d2
                       → binders-unique (d1 ∘ d2)
      BUCast : ∀{d τ1 τ2} → binders-unique d
                           → binders-unique (d ⟨ τ1 ⇒ τ2 ⟩)
      BUFailedCast : ∀{d τ1 τ2} → binders-unique d
                                 → binders-unique (d ⟨ τ1 ⇒⦇⦈⇏ τ2 ⟩)
      BUFst  : ∀{d} →
               binders-unique d →
               binders-unique (fst d)
      BUSnd  : ∀{d} →
               binders-unique d →
               binders-unique (snd d)
      BUPair : ∀{d1 d2} →
               binders-unique d1 →
               binders-unique d2 →
               binders-disjoint d1 d2 →
               binders-unique ⟨ d1 , d2 ⟩

  _⇓_ : iexp → iexp → Set
  d1 ⇓ d2 = (d1 ↦* d2 × d2 final)

  -- this is the decoding function, so half the iso. this won't work long term
  postulate
    _↑_ : iexp → eexp → Set
    _↓_ : eexp → iexp → Set
    iso : Set
    Exp : typ

-- naming conventions:
--
-- type contexts, tctx, are named Γ (because they always are)
-- hole contextst, ??, are named Δ
--
-- types, typ, are named τ
-- unexpanded expressions, uexp, are named ê (for "_e_xpression but also following the POPL17 notation)
-- expanded expressions, eexp, are named e (for "_e_xpression")
-- internal expressions, iexp, are named d (because they have a _d_ynamics)
-- splices are named ψ

  -- function-like livelit context well-formedness
  mutual
    livelitctx = Σ[ Φ' ∈ livelitdef ctx ] (Φ' livelitctx')

    data _livelitctx' : (Φ' : livelitdef ctx) → Set where
      PhiWFEmpty     : ∅ livelitctx'
      PhiWFMac       : ∀{a π} →
                          (Φ : livelitctx) →
                           a # π1 Φ →
                           (π1 Φ ,, (a , π)) livelitctx'

  _₁ : (Φ : livelitctx) → livelitdef ctx
  _₁ = π1

  infixr 25 _₁

  _,,_::_⦅given_⦆ : (Φ : livelitctx) →
                 (a : livelitname) →
                 livelitdef →
                 a # (Φ)₁ →
                 livelitctx
  Φ ,, a :: π ⦅given #h ⦆ = ((Φ)₁ ,, (a , π) , PhiWFMac Φ #h)

  -- livelit expansion
  mutual
    data _,_⊢_~~>_⇒_ : (Φ : livelitctx) →
                       (Γ : tctx) →
                       (ê : uexp) →
                       (e : eexp) →
                       (τ : typ) →
                       Set
      where
        SPEConst : ∀{Φ Γ} → Φ , Γ ⊢ c ~~> c ⇒ b
        SPEAsc   : ∀{Φ Γ ê e τ} →
                           Φ , Γ ⊢ ê ~~> e ⇐ τ →
                           Φ , Γ ⊢ (ê ·: τ) ~~> e ·: τ ⇒ τ
        SPEVar   : ∀{Φ Γ x τ} →
                           (x , τ) ∈ Γ →
                           Φ , Γ ⊢ (X x) ~~> (X x) ⇒ τ
        SPELam   : ∀{Φ Γ x e τ1 τ2 ê} →
                           x # Γ →
                           Φ , Γ ,, (x , τ1) ⊢ ê ~~> e ⇒ τ2 →
                           Φ , Γ ⊢ (·λ_[_]_ x τ1 ê) ~~> (·λ x [ τ1 ] e) ⇒ (τ1 ==> τ2)
        SPEAp    : ∀{Φ Γ ê1 ê2 τ1 τ2 τ e1 e2} →
                           Φ , Γ ⊢ ê1 ~~> e1 ⇒ τ1 →
                           τ1 ▸arr τ2 ==> τ →
                           Φ , Γ ⊢ ê2 ~~> e2 ⇐ τ2 →
                           holes-disjoint e1 e2 →
                           Φ , Γ ⊢ ê1 ∘ ê2 ~~> e1 ∘ e2 ⇒ τ
        SPEHole  : ∀{Φ Γ u} → Φ , Γ ⊢ ⦇⦈[ u ] ~~> ⦇⦈[ u ] ⇒ ⦇·⦈
        SPNEHole : ∀{Φ Γ ê e τ u} →
                           hole-name-new e u →
                           Φ , Γ ⊢ ê ~~> e ⇒ τ →
                           Φ , Γ ⊢ ⦇⌜ ê ⌟⦈[ u ] ~~> ⦇⌜ e ⌟⦈[ u ] ⇒ ⦇·⦈
        SPEFst   : ∀{Φ Γ ê e τ τ1 τ2} →
                           Φ , Γ ⊢ ê ~~> e ⇒ τ →
                           τ ▸prod τ1 ⊗ τ2 →
                           Φ , Γ ⊢ fst ê ~~> fst e ⇒ τ1
        SPESnd   : ∀{Φ Γ ê e τ τ1 τ2} →
                           Φ , Γ ⊢ ê ~~> e ⇒ τ →
                           τ ▸prod τ1 ⊗ τ2 →
                           Φ , Γ ⊢ snd ê ~~> snd e ⇒ τ2
        SPEPair  : ∀{Φ Γ ê1 ê2 τ1 τ2 e1 e2} →
                           Φ , Γ ⊢ ê1 ~~> e1 ⇒ τ1 →
                           Φ , Γ ⊢ ê2 ~~> e2 ⇒ τ2 →
                           holes-disjoint e1 e2 →
                           Φ , Γ ⊢ ⟨ ê1 , ê2 ⟩ ~~> ⟨ e1 , e2 ⟩ ⇒ τ1 ⊗ τ2
        SPEApLivelit  : ∀{Φ Γ a dm π denc eexpanded τsplice psplice esplice u} →
                         holes-disjoint eexpanded esplice →
                         freshΓ Γ eexpanded →
                         (a , π) ∈ (Φ)₁ →
                         ∅ , ∅ ⊢ dm :: (livelitdef.model-type π) →
                         ((livelitdef.expand π) ∘ dm) ⇓ denc →
                         denc ↑ eexpanded →
                         Φ , Γ ⊢ psplice ~~> esplice ⇐ τsplice →
                         ∅ ⊢ eexpanded <= τsplice ==> (livelitdef.expansion-type π) →
                         Φ , Γ ⊢ ＄ a ⟨ dm ⁏ (τsplice , psplice) :: [] ⟩[ u ] ~~> ((eexpanded ·: τsplice ==> livelitdef.expansion-type π) ∘ esplice) ⇒ livelitdef.expansion-type π

    data _,_⊢_~~>_⇐_ : (Φ : livelitctx) →
                       (Γ : tctx) →
                       (ê : uexp) →
                       (e : eexp) →
                       (τ : typ) →
                       Set
      where
        APELam     : ∀{Φ Γ x e τ τ1 τ2 ê} →
                           x # Γ →
                           τ ▸arr τ1 ==> τ2 →
                           Φ , Γ ,, (x , τ1) ⊢ ê ~~> e ⇐ τ2 →
                           Φ , Γ ⊢ (·λ x ê) ~~> (·λ x e) ⇐ τ
        APESubsume : ∀{Φ Γ ê e τ τ'} →
                           Φ , Γ ⊢ ê ~~> e ⇒ τ' →
                           τ ~ τ' →
                           Φ , Γ ⊢ ê ~~> e ⇐ τ
