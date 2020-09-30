open import Prelude
open import core

module lemmas-matching where
  -- matching produces unique answers for arrows, sums, and products
  ▸arr-unicity : ∀{ t t2 t3 } →
                 t ▸arr t2 →
                 t ▸arr t3 →
                 t2 == t3
  ▸arr-unicity MAHole MAHole = refl
  ▸arr-unicity MAArr MAArr = refl

  ▸prod-unicity : ∀{ t t2 t3 } →
                 t ▸prod t2 →
                 t ▸prod t3 →
                 t2 == t3
  ▸prod-unicity MPHole MPHole = refl
  ▸prod-unicity MPProd MPProd = refl

  -- if there's a matches, then it's consistent with the least restrictive
  -- function type
  matchconsisthole : ∀{t t'} →
                 t ▸arr t' →
                 t ~ (⦇·⦈ ==> ⦇·⦈)
  matchconsisthole MAHole = TCHole2
  matchconsisthole MAArr = TCArr TCHole1 TCHole1

  match-consist : ∀{τ1 τ2} → τ1 ▸arr τ2 → (τ2 ~ τ1)
  match-consist MAHole = TCHole1
  match-consist MAArr = TCRefl

  match-unicity : ∀{ τ τ1 τ2} → τ ▸arr τ1 → τ ▸arr τ2 → τ1 == τ2
  match-unicity MAHole MAHole = refl
  match-unicity MAArr MAArr = refl

  matchconsistholeprod : ∀{t t'} →
                     t ▸prod t' →
                     t ~ (⦇·⦈ ⊗ ⦇·⦈)
  matchconsistholeprod MPHole = TCHole2
  matchconsistholeprod MPProd = TCProd TCHole1 TCHole1

  match-consist-prod : ∀{τ1 τ2} → τ1 ▸prod τ2 → (τ2 ~ τ1)
  match-consist-prod MPHole = TCHole1
  match-consist-prod MPProd = TCRefl

  match-unicity-prod : ∀{ τ τ1 τ2} → τ ▸prod τ1 → τ ▸prod τ2 → τ1 == τ2
  match-unicity-prod MPHole MPHole = refl
  match-unicity-prod MPProd MPProd = refl
