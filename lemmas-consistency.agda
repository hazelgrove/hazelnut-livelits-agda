open import Prelude
open import core

module lemmas-consistency where
  -- type consistency is symmetric
  ~sym : {t1 t2 : typ} → t1 ~ t2 → t2 ~ t1
  ~sym TCRefl = TCRefl
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)
  ~sym (TCProd h h₁) = TCProd (~sym h) (~sym h₁)

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : typ) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (b ==> b) ⦇·⦈ b TCHole1 TCHole2
  ... | ()

  --  every pair of types is either consistent or not consistent
  ~dec : (t1 t2 : typ) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇·⦈ = Inl TCHole1
  ~dec ⦇·⦈ b = Inl TCHole2
  ~dec ⦇·⦈ (q ==> q₁) = Inl TCHole2
  ~dec ⦇·⦈ (q ⊗ q₁) = Inl TCHole2
    -- num cases
  ~dec b b = Inl TCRefl
  ~dec b (t2 ==> t3) = Inr ICBaseArr1
    -- arrow cases
  ~dec (t1 ==> t2) b = Inr ICBaseArr2
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (ICArr2 y)
  ... | Inr x | _     = Inr (ICArr1 x)
  ~dec b (t2 ⊗ t3) = Inr ICBaseProd1
  ~dec (t1 ==> t2) (t3 ⊗ t4) = Inr ICProdArr1
  ~dec (t1 ⊗ t2) b = Inr ICBaseProd2
  ~dec (t1 ⊗ t2) (t3 ==> t4) = Inr ICProdArr2
  ~dec (t1 ⊗ t2) (t3 ⊗ t4) with ~dec t1 t3 | ~dec t2 t4
  ~dec (t1 ⊗ t2) (t3 ⊗ t4) | Inl x | Inl x₁ = Inl (TCProd x x₁)
  ~dec (t1 ⊗ t2) (t3 ⊗ t4) | Inl x | Inr x₁ = Inr (ICProd2 x₁)
  ~dec (t1 ⊗ t2) (t3 ⊗ t4) | Inr x | Inl x₁ = Inr (ICProd1 x)
  ~dec (t1 ⊗ t2) (t3 ⊗ t4) | Inr x | Inr x₁ = Inr (ICProd1 x)

  -- no pair of types is both consistent and not consistent
  ~apart : {t1 t2 : typ} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  ~apart ICBaseArr1 ()
  ~apart ICBaseArr2 ()
  ~apart (ICArr1 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr1 x) (TCArr y y₁) = ~apart x y
  ~apart (ICArr2 x) TCRefl = ~apart x TCRefl
  ~apart (ICArr2 x) (TCArr y y₁) = ~apart x y₁
  ~apart ICBaseProd1 ()
  ~apart ICBaseProd2 ()
  ~apart ICProdArr1 ()
  ~apart ICProdArr2 ()
  ~apart (ICProd1 h) TCRefl = ~apart h TCRefl
  ~apart (ICProd1 h) (TCProd h₁ h₂) = ~apart h h₁
  ~apart (ICProd2 h) TCRefl = ~apart h TCRefl
  ~apart (ICProd2 h) (TCProd h₁ h₂) = ~apart h h₂

  ~apart-converse : (τ1 τ2 : typ) → (τ1 ~ τ2 → ⊥) → τ1 ~̸ τ2
  ~apart-converse τ1 τ2 ne with ~dec τ1 τ2
  ~apart-converse τ1 τ2 ne    | Inl h      = abort (ne h)
  ~apart-converse τ1 τ2 ne    | Inr h      = h

  ~decPair : (τ1 τ2 τ3 τ4 : typ) → ((τ1 ⊗ τ2) ~ (τ3 ⊗ τ4) → ⊥) → (τ1 ~ τ3 → ⊥) + (τ2 ~ τ4 → ⊥)
  ~decPair τ1 τ2 τ3 τ4 inc with ~apart-converse (τ1 ⊗ τ2) (τ3 ⊗ τ4) inc
  ~decPair τ1 τ2 τ3 τ4 inc    | ICProd1 h                                = Inl (~apart h)
  ~decPair τ1 τ2 τ3 τ4 inc    | ICProd2 h                                = Inr (~apart h)

  ~prod1 : ∀{τ1 τ2 τ3 τ4} → (τ1 ⊗ τ2) ~ (τ3 ⊗ τ4) → τ1 ~ τ3
  ~prod1 TCRefl = TCRefl
  ~prod1 (TCProd h1 h2) = h1

  ~prod2 : ∀{τ1 τ2 τ3 τ4} → (τ1 ⊗ τ2) ~ (τ3 ⊗ τ4) → τ2 ~ τ4
  ~prod2 TCRefl = TCRefl
  ~prod2 (TCProd h1 h2) = h2
