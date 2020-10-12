open import Prelude
open import core

open import progress-checks

module finality where
  finality : Σ[ d ∈ iexp ] (d final × (Σ[ d' ∈ iexp ] (d ↦ d'))) → ⊥
  finality (π1 , π2 , π3 , π4) = final-not-step π2 (π3 , π4)

  -- a slight restatement of the above, generalizing it to the
  -- multistep judgement
  finality* : ∀{d d'} → d final → d ↦* d' → d == d'
  finality* fin MSRefl = refl
  finality* fin (MSStep x ms) = abort (final-not-step fin (_ , x))
