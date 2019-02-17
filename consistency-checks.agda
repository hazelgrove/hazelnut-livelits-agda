open import Prelude
open import core

module consistency-checks where
  incondecp : (τ1 τ2 τ3 τ4 : htyp) → ((τ1 ⊗ τ2) ~ (τ3 ⊗ τ4) → ⊥) → (τ1 ~ τ3 → ⊥) + (τ2 ~ τ4 → ⊥)
  incondecp τ1 τ2 τ3 τ4 inc = {!!}

  notcon-incon : (τ1 τ2 : htyp) → (τ1 ~ τ2 → ⊥) → τ1 ~̸ τ2
  notcon-incon b b notcon = abort (notcon TCRefl)
  notcon-incon b ⦇⦈ notcon = abort (notcon TCHole1)
  notcon-incon b (τ2 ==> τ3) notcon = ICBaseArr1
  notcon-incon b (τ2 ⊗ τ3) notcon = ICBaseProd1
  notcon-incon ⦇⦈ b notcon = abort (notcon TCHole2)
  notcon-incon ⦇⦈ ⦇⦈ notcon = abort (notcon TCRefl)
  notcon-incon ⦇⦈ (τ2 ==> τ3) notcon = abort (notcon TCHole2)
  notcon-incon ⦇⦈ (τ2 ⊗ τ3) notcon = abort (notcon TCHole2)
  notcon-incon (τ1 ==> τ2) b notcon = ICBaseArr2
  notcon-incon (τ1 ==> τ2) ⦇⦈ notcon = abort (notcon TCHole1)
  notcon-incon (τ1 ==> τ2) (τ3 ==> τ4) notcon = {!!}
  notcon-incon (τ1 ==> τ2) (τ3 ⊗ τ4) notcon = ICProdArr1
  notcon-incon (τ1 ⊗ τ2) b notcon = ICBaseProd2
  notcon-incon (τ1 ⊗ τ2) ⦇⦈ notcon = abort (notcon TCHole1)
  notcon-incon (τ1 ⊗ τ2) (τ3 ==> τ4) notcon = ICProdArr2
  notcon-incon (τ1 ⊗ τ2) (τ3 ⊗ τ4) notcon = {!!}

  incon-notcon : (τ1 τ2 : htyp) → τ1 ~̸ τ2 → (τ1 ~ τ2 → ⊥)
  incon-notcon = {!!}
