open import Prelude
open import Nat
open import List

module contexts (A : Set) where
  -- variables are named with naturals in ė. therefore we represent
  -- contexts as functions from names for variables (nats) to possible
  -- bindings.

  infixl 5  _,_⦂_

  -- ripping this off from pfla.github.io
  data ctx : Set where
    ∅ : ctx
    _,_⦂_ : ctx → Nat → A → ctx
    _∪_ : ctx → ctx → ctx

  infixr 100 ■_⦂_
  ■_⦂_  : Nat → A → ctx
  ■ x ⦂ a = ∅ , x ⦂ a

  -- apartness for contexts
  data _#_ : (n : Nat) → (Γ : ctx) → Set where
    #∅ : {x : Nat} → x # ∅
    #, : {x y : Nat} {a : A} {Γ : ctx} →
           x ≠ y →
           x # Γ →
           x # (Γ , y ⦂ a)
    #∪ : {x : Nat} {Γ1 Γ2 : ctx} →
           x # Γ1 →
           x # Γ2 →
           x # (Γ1 ∪ Γ2)

  data dom : (n : Nat) → (Γ : ctx) → Set where
    D,1 : {x : Nat} {a : A} {Γ : ctx} →
           dom x (Γ , x ⦂ a)
    D,2 : {x y : Nat} {a : A} {Γ : ctx} →
           x ≠ y → -- hmm
           dom x Γ →
           dom x (Γ , y ⦂ a)
    D∪ : {x : Nat} {Γ1 Γ2 : ctx} →
           (dom x Γ1 + dom x Γ2) →
           dom x (Γ1 ∪ Γ2)

  -- disjoint contexts are those which share no mappings
  _##_ : ctx → ctx → Set
  _##_ Γ Γ'  = ((n : Nat) → dom n Γ → n # Γ') × ((n : Nat) → dom n Γ' → n # Γ)

  infix  4  _⦂_∈_
  data _⦂_∈_ : Nat → A → ctx → Set where
    ∈hd : ∀{x a Γ} → x ⦂ a ∈ (Γ , x ⦂ a)
    ∈tl : ∀{ Γ x y a b } →
         x ≠ y →
         x ⦂ a ∈ Γ →
         x ⦂ a ∈ (Γ , y ⦂ b)
    ∈union : ∀{x a Γ1 Γ2} →
         Γ1 ## Γ2 →
         (x ⦂ a ∈ Γ1 + x ⦂ a ∈ Γ2) →
         x ⦂ a ∈ Γ1 ∪ Γ2

  apart-notin : ∀{x Γ τ} → x # Γ → x ⦂ τ ∈ Γ → ⊥
  apart-notin #∅ ()
  apart-notin (#, x₁ apt) ∈hd = x₁ refl
  apart-notin (#, x₁ apt) (∈tl x₂ xtin) = apart-notin apt xtin
  apart-notin (#∪ apt apt₁) (∈union x₁ (Inl x₂)) = apart-notin apt x₂
  apart-notin (#∪ apt apt₁) (∈union x₁ (Inr x₂)) = apart-notin apt₁ x₂

  -- the domain of a context is those naturals which cuase it to emit some τ
  -- this is false; you can form contexts that you can't look up into, i.e. ones that aren't disjoint
  -- dom-check : (Γ : ctx) → (x : Nat) → dom x Γ →  Σ[ τ ∈ A ] (x ⦂ τ ∈ Γ)
  -- dom-check .(_ , x ⦂ _) x D,1 = _ , ∈hd
  -- dom-check .(_ , _ ⦂ _) x (D,2 x₁ D) = _ , ∈tl x₁ (π2 (dom-check _ _ D))
  -- dom-check .(_ ∪ _) x (D∪ (Inl x₁)) with dom-check _ _ x₁
  -- dom-check .(_ ∪ _) x (D∪ (Inl x₁)) | π3 , π4 = π3 , ∈union {!!} (Inl π4)
  -- dom-check .(_ ∪ _) x (D∪ (Inr x₁)) with dom-check _ _ x₁
  -- dom-check .(_ ∪ _) x (D∪ (Inr x₁)) | π3 , π4 = π3 , ∈union {!!} (Inr π4)

  in-dom : ∀{x τ Γ} → (x ⦂ τ ∈ Γ) → dom x Γ
  in-dom ∈hd = D,1
  in-dom (∈tl x₁ xin) = D,2 x₁ (in-dom xin)
  in-dom (∈union x₁ (Inl x₂)) = D∪ (Inl (in-dom x₂))
  in-dom (∈union x₁ (Inr x₂)) = D∪ (Inr (in-dom x₂))


  -- this packages up an appeal to context memebership into a form that
  -- lets us retain more information
  ctxindirect : (Γ : ctx) (x : Nat) → dom x Γ + x # Γ
  ctxindirect ∅ x = Inr #∅
  ctxindirect (Γ , y ⦂ τ) x with natEQ x y | ctxindirect Γ x
  ctxindirect (Γ , y ⦂ τ) .y | Inl refl | pp = Inl D,1
  ctxindirect (Γ , y ⦂ τ) x | Inr x₁ | Inl x₂ = Inl (D,2 x₁ x₂)
  ctxindirect (Γ , y ⦂ τ) x | Inr x₁ | Inr x₂ = Inr (#, x₁ x₂)
  ctxindirect (Γ1 ∪ Γ2) x with ctxindirect Γ1 x | ctxindirect Γ2 x
  ctxindirect (Γ1 ∪ Γ2) x | Inl x₁ | Inl x₂ = Inl (D∪ (Inl x₁))
  ctxindirect (Γ1 ∪ Γ2) x | Inl x₁ | Inr x₂ = Inl (D∪ (Inl x₁)) -- maybe a problem
  ctxindirect (Γ1 ∪ Γ2) x | Inr x₁ | Inl x₂ = Inl (D∪ (Inr x₂))
  ctxindirect (Γ1 ∪ Γ2) x | Inr x₁ | Inr x₂ = Inr (#∪ x₁ x₂)

  -- contexts give at most one binding for each variable
  ctxunicity : {Γ : ctx} {n : Nat} {t t' : A} →
               n ⦂ t ∈ Γ →
               n ⦂ t' ∈ Γ →
               t == t'
  ctxunicity ∈hd ∈hd = refl
  ctxunicity ∈hd (∈tl x in2) = abort (x refl)
  ctxunicity (∈tl x in1) ∈hd = abort (x refl)
  ctxunicity (∈tl x in1) (∈tl x₁ in2) = ctxunicity in1 in2
  ctxunicity (∈union x (Inl x₁)) (∈union x₂ (Inl x₃)) = ctxunicity x₁ x₃
  ctxunicity (∈union x (Inl x₁)) (∈union x₂ (Inr x₃)) = abort (apart-notin (π2 x₂ _ (in-dom x₃)) x₁)
  ctxunicity (∈union x (Inr x₁)) (∈union x₂ (Inl x₃)) = abort (apart-notin (π2 x₂ _ (in-dom x₁)) x₃)
  ctxunicity (∈union x (Inr x₁)) (∈union x₂ (Inr x₃)) = ctxunicity x₁ x₃


  -- lem-dom-union1 : {C1 C2 : ctx} {x : Nat} →
  --                                   C1 ## C2 →
  --                                   dom C1 x →
  --                                   (C1 ∪ C2) x == C1 x
  -- lem-dom-union1 {A} {C1} {C2} {x} (d1 , d2) D with C1 x
  -- lem-dom-union1 (d1 , d2) D | Some x₁ = refl
  -- lem-dom-union1 (d1 , d2) D | None = abort (somenotnone (! (π2 D)))

  -- lem-dom-union2 : {A : Set} {C1 C2 : A ctx} {x : Nat} →
  --                                   C1 ## C2 →
  --                                   dom C1 x →
  --                                   (C2 ∪ C1) x == C1 x
  -- lem-dom-union2 {A} {C1} {C2} {x} (d1 , d2) D with ctxindirect C2 x
  -- lem-dom-union2 {A} {C1} {C2} {x} (d1 , d2) D | Inl x₁ = abort (somenotnone (! (π2 x₁) · d1 x D ))
  -- lem-dom-union2 {A} {C1} {C2} {x} (d1 , d2) D | Inr x₁ with C2 x
  -- lem-dom-union2 (d1 , d2) D | Inr x₂ | Some x₁ = abort (somenotnone x₂)
  -- lem-dom-union2 (d1 , d2) D | Inr x₁ | None = refl

  -- -- if the contexts in question are disjoint, then union is commutative
  -- ∪comm : (C1 C2 : ctx) → C1 ## C2 → (C1 ∪ C2) == (C2 ∪ C1)
  -- ∪comm ∅ ∅ (d1 , d2) = refl
  -- ∪comm ∅ (C2 , x ⦂ x₁) (d1 , d2) = refl
  -- ∪comm (C1 , x ⦂ x₁) ∅ (d1 , d2) = refl
  -- ∪comm (C1 , x ⦂ x₁) (C2 , x₂ ⦂ x₃) (d1 , d2) with ∪comm C1 C2 {!!}
  -- ... | qq = {!!}
  --   where
  --     ##-smaller : ∀{C1 C2 x y a b} → (C1 , x ⦂ a) ## (C2 , y ⦂ b) → C1 ## C2
  --     ##-smaller (d1 , d2) = {!!}

-- funext guts
  --   where
  --     lem-apart-union1 : {A : Set} (C1 C2 : A ctx) (x : Nat) → x # C1 → x # C2 → x # (C1 ∪ C2)
  --     lem-apart-union1 C1 C2 x apt1 apt2 with C1 x
  --     lem-apart-union1 C1 C2 x apt1 apt2 | Some x₁ = abort (somenotnone apt1)
  --     lem-apart-union1 C1 C2 x apt1 apt2 | None = apt2

  --     lem-apart-union2 : {A : Set} (C1 C2 : A ctx) (x : Nat) → x # C1 → x # C2 → x # (C2 ∪ C1)
  --     lem-apart-union2 C1 C2 x apt1 apt2 with C2 x
  --     lem-apart-union2 C1 C2 x apt1 apt2 | Some x₁ = abort (somenotnone apt2)
  --     lem-apart-union2 C1 C2 x apt1 apt2 | None = apt1

  --     guts : (x : Nat) → (C1 ∪ C2) x == (C2 ∪ C1) x
  --     guts x with ctxindirect C1 x | ctxindirect C2 x
  --     guts x | Inl (π1 , π2) | Inl (π3 , π4) = abort (somenotnone (! π4 · d1 x (π1 , π2)))
  --     guts x | Inl x₁ | Inr x₂ = tr (λ qq → qq == (C2 ∪ C1) x) (! (lem-dom-union1 (d1 , d2) x₁)) (tr (λ qq → C1 x == qq) (! (lem-dom-union2 (d1 , d2) x₁)) refl)
  --     guts x | Inr x₁ | Inl x₂ = tr (λ qq → (C1 ∪ C2) x == qq) (! (lem-dom-union1 (d2 , d1) x₂)) (tr (λ qq → qq == C2 x) (! (lem-dom-union2 (d2 , d1) x₂)) refl)
  --     guts x | Inr x₁ | Inr x₂ = tr (λ qq → qq == (C2 ∪ C1) x) (! (lem-apart-union1 C1 C2 x x₁ x₂)) (tr (λ qq → None == qq) (! (lem-apart-union2 C1 C2 x x₁ x₂)) refl)


  -- an element in the left of a union is in the union
  -- x∈∪l : {Γ Γ' : ctx} {x : Nat} {τ : A} → x ⦂ τ ∈ Γ → x ⦂ τ ∈ (Γ ∪ Γ')
  -- x∈∪l ∈hd = ∈union {!!} {!!}
  -- x∈∪l (∈tl x₁ xin) = ∈union {!!} {!!}
  -- x∈∪l (∈union x₁ x₂) = ∈union {!!} {!!}

  -- -- an element in the right of a union is in the union as long as the
  -- -- contexts are disjoint; this asymmetry reflects the asymmetry in the
  -- -- definition of union
  -- x∈∪r : {A : Set} → (Γ Γ' : A ctx) (n : Nat) (x : A) →
  --                            (n , x) ∈ Γ' →
  --                            Γ' ## Γ →
  --                            (n , x) ∈ (Γ ∪ Γ')
  -- x∈∪r Γ Γ' n x nx∈ disj = tr (λ qq → (n , x) ∈ qq) (∪comm _ _ disj) (x∈∪l Γ' Γ n x nx∈)

  -- an element is in the context formed with just itself
  -- x∈■ : (n : Nat) (a : A) → n ⦂ a ∈ (■ (n , a))
  -- x∈■ n a = hd

  -- -- if an index is in the domain of a singleton context, it's the only
  -- -- index in the context
  -- lem-dom-eq : {A : Set} {y : A} {n m : Nat} →
  --                                dom (■ (m , y)) n →
  --                                n == m
  -- lem-dom-eq {n = n} {m = m} (π1 , π2) with natEQ m n
  -- lem-dom-eq (π1 , π2) | Inl refl = refl
  -- lem-dom-eq (π1 , π2) | Inr x = abort (somenotnone (! π2))

  -- -- a singleton context formed with an index apart from a context is
  -- -- disjoint from that context
  -- lem-apart-sing-disj : {A : Set} {n : Nat} {a : A} {Γ : A ctx} →
  --                                    n # Γ →
  --                                    (■ (n , a)) ## Γ
  -- lem-apart-sing-disj {A} {n} {a} {Γ} apt = asd1 , asd2
  --   where
  --     asd1 : (n₁ : Nat) → dom (■ (n , a)) n₁ → n₁ # Γ
  --     asd1 m d with lem-dom-eq  d
  --     asd1 .n d | refl = apt

  --     asd2 : (n₁ : Nat) → dom Γ n₁ → n₁ # (■ (n , a))
  --     asd2 m (π1 , π2) with natEQ n m
  --     asd2 .n (π1 , π2) | Inl refl = abort (somenotnone (! π2 · apt ))
  --     asd2 m (π1 , π2) | Inr x = refl

  -- -- the only index of a singleton context is in its domain
  -- lem-domsingle : {A : Set} (p : Nat) (q : A) → dom (■ (p , q)) p
  -- lem-domsingle p q with natEQ p p
  -- lem-domsingle p q | Inl refl = q , refl
  -- lem-domsingle p q | Inr x₁ = abort (x₁ refl)


  -- -- dual of above
  -- lem-disj-sing-apart : {A : Set} {n : Nat} {a : A} {Γ : A ctx} →
  --                                    (■ (n , a)) ## Γ →
  --                                    n # Γ
  -- lem-disj-sing-apart {A} {n} {a} {Γ} (d1 , d2) = d1 n (lem-domsingle n a)

  -- -- the singleton context can only produce one non-none result
  -- lem-insingeq : {A : Set} {x x' : Nat} {τ τ' : A} →
  --                             (■ (x , τ)) x' == Some τ' →
  --                             τ == τ'
  -- lem-insingeq {A} {x} {x'} {τ} {τ'} eq with lem-dom-eq (τ' , eq)
  -- lem-insingeq {A} {x} {.x} {τ} {τ'} eq | refl with natEQ x x
  -- lem-insingeq refl | refl | Inl refl = refl
  -- lem-insingeq eq | refl | Inr x₁ = abort (somenotnone (! eq))

  -- -- if an index doesn't appear in a context, and the union of that context
  -- -- with a singleton does produce a result, it must have come from the singleton
  -- lem-apart-union-eq : {A : Set} {Γ : A ctx} {x x' : Nat} {τ τ' : A} →
  --                                   x' # Γ →
  --                                   (Γ ∪ ■ (x , τ)) x' == Some τ' →
  --                                   τ == τ'
  -- lem-apart-union-eq {A} {Γ} {x} {x'} {τ} {τ'} apart eq with Γ x'
  -- lem-apart-union-eq apart eq | Some x = abort (somenotnone apart)
  -- lem-apart-union-eq apart eq | None = lem-insingeq eq

  -- -- if an index not in a singleton context produces a result from that
  -- -- singleton unioned with another context, the result must have come from
  -- -- the other context
  -- lem-neq-union-eq : {A : Set} {Γ : A ctx} {x x' : Nat} {τ τ' : A} →
  --                                   x' ≠ x →
  --                                   (Γ ∪ ■ (x , τ)) x' == Some τ' →
  --                                   Γ x' == Some τ'
  -- lem-neq-union-eq {A} {Γ} {x} {x'} {τ} {τ'} neq eq with Γ x'
  -- lem-neq-union-eq neq eq | Some x = eq
  -- lem-neq-union-eq {A} {Γ} {x} {x'} {τ} {τ'} neq eq | None with natEQ x x'
  -- lem-neq-union-eq neq eq | None | Inl x₁ = abort ((flip neq) x₁)
  -- lem-neq-union-eq neq eq | None | Inr x₁ = abort (somenotnone (! eq))

  -- -- extending a context with a new index produces the result paired with
  -- -- that index.
  -- ctx-top : {A : Set} → (Γ : A ctx) (n : Nat) (a : A) →
  --                                      (n # Γ) →
  --                                      (n , a) ∈ (Γ ,, (n , a))
  -- ctx-top Γ n a apt = x∈∪r Γ (■ (n , a)) n a (x∈■ n a) (lem-apart-sing-disj apt)

  -- --- lemmas building up to a proof of associativity of ∪
  -- ctxignore1 : {A : Set} (x : Nat) (C1 C2 : A ctx) → x # C1 → (C1 ∪ C2) x == C2 x
  -- ctxignore1 x C1 C2 apt with ctxindirect C1 x
  -- ctxignore1 x C1 C2 apt | Inl x₁ = abort (somenotnone (! (π2 x₁) · apt))
  -- ctxignore1 x C1 C2 apt | Inr x₁ with C1 x
  -- ctxignore1 x C1 C2 apt | Inr x₂ | Some x₁ = abort (somenotnone (x₂))
  -- ctxignore1 x C1 C2 apt | Inr x₁ | None = refl

  -- ctxignore2 : {A : Set} (x : Nat) (C1 C2 : A ctx) → x # C2 → (C1 ∪ C2) x == C1 x
  -- ctxignore2 x C1 C2 apt with ctxindirect C2 x
  -- ctxignore2 x C1 C2 apt | Inl x₁ = abort (somenotnone (! (π2 x₁) · apt))
  -- ctxignore2 x C1 C2 apt | Inr x₁ with C1 x
  -- ctxignore2 x C1 C2 apt | Inr x₂ | Some x₁ = refl
  -- ctxignore2 x C1 C2 apt | Inr x₁ | None = x₁

  -- ctxcollapse1 : {A : Set} → (C1 C2 C3 : A ctx) (x : Nat) →
  --              (x # C3) →
  --              (C2 ∪ C3) x == C2 x →
  --              (C1 ∪ (C2 ∪ C3)) x == (C1 ∪ C2) x
  -- ctxcollapse1 C1 C2 C3 x apt eq with C2 x
  -- ctxcollapse1 C1 C2 C3 x apt eq | Some x₁ with C1 x
  -- ctxcollapse1 C1 C2 C3 x apt eq | Some x₂ | Some x₁ = refl
  -- ctxcollapse1 C1 C2 C3 x apt eq | Some x₁ | None with C2 x
  -- ctxcollapse1 C1 C2 C3 x apt eq | Some x₂ | None | Some x₁ = refl
  -- ctxcollapse1 C1 C2 C3 x apt eq | Some x₁ | None | None = apt
  -- ctxcollapse1 C1 C2 C3 x apt eq | None with C1 x
  -- ctxcollapse1 C1 C2 C3 x apt eq | None | Some x₁ = refl
  -- ctxcollapse1 C1 C2 C3 x apt eq | None | None with C2 x
  -- ctxcollapse1 C1 C2 C3 x apt eq | None | None | Some x₁ = refl
  -- ctxcollapse1 C1 C2 C3 x apt eq | None | None | None = eq

  -- ctxcollapse2 : {A : Set} → (C1 C2 C3 : A ctx) (x : Nat) →
  --                (x # C2) →
  --                (C2 ∪ C3) x == C3 x →
  --                (C1 ∪ (C2 ∪ C3)) x == (C1 ∪ C3) x
  -- ctxcollapse2 C1 C2 C3 x apt eq with C1 x
  -- ctxcollapse2 C1 C2 C3 x apt eq | Some x₁ = refl
  -- ctxcollapse2 C1 C2 C3 x apt eq | None with C2 x
  -- ctxcollapse2 C1 C2 C3 x apt eq | None | Some x₁ = eq
  -- ctxcollapse2 C1 C2 C3 x apt eq | None | None = refl

  -- ctxcollapse3 : {A : Set} → (C1 C2 C3 : A ctx) (x : Nat) →
  --                (x # C2) →
  --                ((C1 ∪ C2) ∪ C3) x == (C1 ∪ C3) x
  -- ctxcollapse3 C1 C2 C3 x apt with C1 x
  -- ctxcollapse3 C1 C2 C3 x apt | Some x₁ = refl
  -- ctxcollapse3 C1 C2 C3 x apt | None with C2 x
  -- ctxcollapse3 C1 C2 C3 x apt | None | Some x₁ = abort (somenotnone apt)
  -- ctxcollapse3 C1 C2 C3 x apt | None | None = refl

  -- -- if a union of a singleton and a ctx produces no result, the argument
  -- -- index must be apart from the ctx and disequal to the index of the
  -- -- singleton
  -- lem-union-none : {A : Set} {Γ : A ctx} {a : A} {x x' : Nat}
  --                     → (Γ ∪ ■ (x , a)) x' == None
  --                     → (x ≠ x') × (x' # Γ)
  -- lem-union-none {A} {Γ} {a} {x} {x'} emp with ctxindirect Γ x'
  -- lem-union-none {A} {Γ} {a} {x} {x'} emp | Inl (π1 , π2) with Γ x'
  -- lem-union-none emp | Inl (π1 , π2) | Some x = abort (somenotnone emp)
  -- lem-union-none {A} {Γ} {a} {x} {x'} emp | Inl (π1 , π2) | None with natEQ x x'
  -- lem-union-none emp | Inl (π1 , π2) | None | Inl x₁ = abort (somenotnone (! π2))
  -- lem-union-none emp | Inl (π1 , π2) | None | Inr x₁ = x₁ , refl
  -- lem-union-none {A} {Γ} {a} {x} {x'} emp | Inr y with Γ x'
  -- lem-union-none emp | Inr y | Some x = abort (somenotnone emp)
  -- lem-union-none {A} {Γ} {a} {x} {x'} emp | Inr y | None with natEQ x x'
  -- lem-union-none emp | Inr y | None | Inl refl = abort (somenotnone emp)
  -- lem-union-none emp | Inr y | None | Inr x₁ = x₁ , refl

  -- -- converse of lem-union-none
  -- lem-none-union : {A : Set} {Γ : A ctx} {a : A} {x x' : Nat}
  --                     → (x ≠ x')
  --                     → (x' # Γ)
  --                     → (Γ ∪ ■ (x , a)) x' == None
  -- lem-none-union {A} {Γ} {a} {x} {x'} h₁ h₂ with ctxindirect (■ (x , a)) x'
  -- lem-none-union {A} {Γ} {a} {x} {x'} h₁ h₂    | Inl (a' , h)               = abort (somenotnone (!( lem-neq-union-eq (flip h₁) (tr (λ y → y == Some a') refl h))))
  -- lem-none-union {A} {Γ} {a} {x} {x'} h₁ h₂    | Inr h                      = (ctxignore1 x' Γ (■ (x , a)) h₂) · h

  -- ∪assoc : {A : Set} (C1 C2 C3 : A ctx) → (C2 ## C3) → (C1 ∪ C2) ∪ C3 == C1 ∪ (C2 ∪ C3)
  -- ∪assoc C1 C2 C3 (d1 , d2) = funext guts
  --   where
  --     case2 : (x : Nat) → x # C3 → dom C2 x → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
  --     case2 x apt dom = (ctxignore2 x (C1 ∪ C2) C3 apt) ·
  --                       ! (ctxcollapse1 C1 C2 C3 x apt (lem-dom-union1 (d1 , d2) dom))

  --     case34 : (x : Nat) → x # C2 → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
  --     case34 x apt = ctxcollapse3 C1 C2 C3 x apt ·
  --                       ! (ctxcollapse2 C1 C2 C3 x apt (ctxignore1 x C2 C3 apt))

  --     guts : (x : Nat) → ((C1 ∪ C2) ∪ C3) x == (C1 ∪ (C2 ∪ C3)) x
  --     guts x with ctxindirect C2 x | ctxindirect C3 x
  --     guts x | Inl (π1 , π2) | Inl (π3 , π4) = abort (somenotnone (! π4 · d1 x (π1 , π2)))
  --     guts x | Inl x₁ | Inr x₂ = case2 x x₂ x₁
  --     guts x | Inr x₁ | Inl x₂ = case34 x x₁
  --     guts x | Inr x₁ | Inr x₂ = case34 x x₁

  -- -- if x is apart from either part of a union, the answer comes from the other one
  -- lem-dom-union-apt1 : {A : Set} {Δ1 Δ2 : A ctx} {x : Nat} {y : A} → x # Δ1 → ((Δ1 ∪ Δ2) x == Some y) → (Δ2 x == Some y)
  -- lem-dom-union-apt1 {A} {Δ1} {Δ2} {x} {y} apt xin with Δ1 x
  -- lem-dom-union-apt1 apt xin | Some x₁ = abort (somenotnone apt)
  -- lem-dom-union-apt1 apt xin | None = xin

  -- lem-dom-union-apt2 : {A : Set} {Δ1 Δ2 : A ctx} {x : Nat} {y : A} → x # Δ2 → ((Δ1 ∪ Δ2) x == Some y) → (Δ1 x == Some y)
  -- lem-dom-union-apt2 {A} {Δ1} {Δ2} {x} {y} apt xin with Δ1 x
  -- lem-dom-union-apt2 apt xin | Some x₁ = xin
  -- lem-dom-union-apt2 apt xin | None = abort (somenotnone (! xin · apt))

  -- -- the empty context is a left and right unit for ∪
  -- ∅∪1 : {Γ : ctx} → ∅ ∪ Γ == Γ
  -- ∅∪1 {∅} = {!!}
  -- ∅∪1 {Γ , x ⦂ x₁} = {!!}
  -- ∅∪1 {Γ ∪ Γ₁} = {!!}

  -- ∅∪2 : {A : Set} {Γ : A ctx} → Γ ∪ ∅ == Γ
  -- ∅∪2 {A} {Γ} = funext guts
  --   where
  --     guts : (x : Nat) → (Γ ∪ ∅) x == Γ x
  --     guts x with Γ x
  --     guts x | Some x₁ = refl
  --     guts x | None = refl
