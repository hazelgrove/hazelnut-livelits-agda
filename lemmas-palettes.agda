open import Nat
open import Prelude
open import core

module lemmas-palettes where
  -- constructor injectivity - why isn't this automatic?
  fpaldef-inj : ∀{π1 π2} → FPalDef π1 == FPalDef π2 → π1 == π2
  fpaldef-inj refl = refl

  -- constructor exclusivity - why isn't this automatic?
  paldef-mnotf : ∀{π1 π2} → MPalDef π1 ≠ FPalDef π2
  paldef-mnotf ()
