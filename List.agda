open import Prelude

module List where
  data List (A : Set) : Set where
    [] : List A
    _::_ : (a : A) (as : List A) → List A

  -- list append, structural on the left
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l₂ = l₂
  (h :: l₁) ++ l₂ = h :: (l₁ ++ l₂)

  -- list membership, as a proposition
  data _inList_ {A : Set} : A → List A → Set where
    InH : {a : A} {as : List A} → a inList (a :: as)
    InT : {a a' : A} {as : List A} → a inList as → a inList (a' :: as)

  -- if everything isn't in a list, it's the empty list
  ∅∈l→l==[] : {A : Set} {l : List A} → ((a : A) → a inList l → ⊥) → l == []
  ∅∈l→l==[] {l = []} h = refl
  ∅∈l→l==[] {l = a' :: as} h = abort (h a' InH)

  -- if a isn't in a cons, it's not in the tail either
  a∉a'::as→a∉as : {A : Set} {as : List A} {a a' : A} →
                  (a inList (a' :: as) → ⊥) →
                   a inList as →
                   ⊥
  a∉a'::as→a∉as h h' = h (InT h')

  -- if x isn't in either side of an append, it's not in the result
  not-in-append-comm : {A : Set} {x : A} {l₁ l₂ : List A} →
                       dec A →
                       (x inList l₁ → ⊥) →
                       (x inList l₂ → ⊥) →
                       x inList (l₁ ++ l₂) → ⊥
  not-in-append-comm {l₁ = []} dec h₁ h₂ h₃ = h₂ h₃
  not-in-append-comm {x = x} {a₁ :: _} dec h₁ h₂ h₃   with  dec a₁ x
  not-in-append-comm {l₁ = l₁} dec h₁ h₂ h₃          | Inl h = h₁ (tr (λ y → y inList l₁) h InH)
  not-in-append-comm dec h₁ h₂ InH                   | Inr h = abort (h refl)
  not-in-append-comm dec h₁ h₂ (InT h₃)              | Inr h = not-in-append-comm dec (a∉a'::as→a∉as h₁) h₂ h₃

  remove-all : {A : Set} → dec A → List A → A → List A
  remove-all dec [] a = []
  remove-all dec (a' :: as) a
    with dec a a' | remove-all dec as a
  ...  | Inl _      | l'                    = l'
  ...  | Inr _      | l'                    = a' :: l'

  -- (homomorphism) removing distributes over append
  remove-all-append-comm : {A : Set} →
                           (dec : dec A) →
                           (l₁ l₂ : List A) →
                           (a : A) →
                           remove-all dec l₁ a ++ remove-all dec l₂ a == remove-all dec (l₁ ++ l₂) a
  remove-all-append-comm dec [] l₂ a = refl
  remove-all-append-comm dec (a₁ :: as₁) l₂ a with dec a a₁ | remove-all-append-comm dec as₁ l₂ a
  remove-all-append-comm dec (a₁ :: as₁) l₂ a    | Inl refl   | h                                      = h
  remove-all-append-comm dec (a₁ :: as₁) l₂ a    | Inr _      | h                                      = ap1 (λ y → a₁ :: y) h

  -- an element isn't in the list that results from removing all instances of it
  remove-all-not-in : {A : Set} →
                      (dec : dec A) →
                      (l : List A) →
                      (a : A) →
                      a inList remove-all dec l a →
                      ⊥
  remove-all-not-in dec [] a ()
  remove-all-not-in dec (a' :: as) a h with    dec a a'
  remove-all-not-in dec (a' :: as) a h       | Inl refl   = remove-all-not-in dec as a' h
  remove-all-not-in dec (a' :: as) .a' InH   | Inr a≠a'   = a≠a' refl
  remove-all-not-in dec (a' :: as) a (InT h) | Inr a≠a'   = remove-all-not-in dec as a h

  -- an element that was never in a list still isn't once you remove any element.
  a∉l→a∉remove-all-l-a' : {A : Set} →
                            {l : List A} →
                            {a a' : A} →
                            (dec : dec A) →
                            (a inList l → ⊥) →
                            a inList remove-all dec l a' →
                            ⊥
  a∉l→a∉remove-all-l-a' {l = []} {a} _ h₁ h₂ = h₁ h₂
  a∉l→a∉remove-all-l-a' {l = lh :: lt} {a} {a'} dec h₁ h₂   with  dec a lh | dec a' lh
  a∉l→a∉remove-all-l-a' {l = lh :: lt} {a} dec h₁ h₂       | Inl a==lh  | _            = h₁ (tr (λ y → a inList (y :: lt) ) a==lh InH)
  a∉l→a∉remove-all-l-a' {l = lh :: lt} dec h₁ h₂       | Inr _      | Inl _        = a∉l→a∉remove-all-l-a' dec (a∉a'::as→a∉as h₁) h₂
  a∉l→a∉remove-all-l-a' {l = lh :: lt} dec h₁ InH    | Inr a≠lh   | Inr _        = a≠lh refl
  a∉l→a∉remove-all-l-a' {l = lh :: lt} dec h₁ (InT h₂) | Inr _      | Inr _        = a∉l→a∉remove-all-l-a' dec (a∉a'::as→a∉as h₁) h₂

  -- if an element is in an append, it's in one side or the other
  inList++ : {A : Set} {x : A} → ∀{l1 l2} → dec A → x inList (l1 ++ l2) → (x inList l1) + (x inList l2)
  inList++ {l1 = []} dec xin = Inr xin
  inList++ {x = x} {l1 = a :: l1} dec inl with dec x a
  inList++ {x = .a} {a :: l1} dec inl | Inl refl = Inl InH
  inList++ {x = .a} {a :: l1} dec InH | Inr x₁ = abort (x₁ refl)
  inList++ {x = x} {a :: l1} dec (InT inl) | Inr x₁ with inList++ {l1 = l1} dec inl
  inList++ {x = x} {a :: l1} dec (InT inl) | Inr x₁ | Inl x₂ = Inl (InT x₂)
  inList++ {x = x} {a :: l1} dec (InT inl) | Inr x₁ | Inr x₂ = Inr x₂
