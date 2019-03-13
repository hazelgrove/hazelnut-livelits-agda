open import Nat
open import Prelude
open import core
open import contexts

open import lemmas-palettes

module palettes-checks where
  -- in a well-formed palette context, the `expand` of all definitions analyzes against the proper type
  palctx-well-typed : ∀{ρ π} →
                       (Φ : palctx) →
                       (ρ , FPalDef π) ∈ (Φ)₁ →
                       ∅ ⊢ fpaldef.expand π <= fpaldef.model-type π ==> fpaldef.splice-type π ==> fpaldef.expansion-type π
  palctx-well-typed (_ , PhiWFEmpty) ()
  palctx-well-typed {ρ}   (_ , PhiWFInductive {ρ'} Φ h1 h2) h3 with natEQ ρ ρ'
  palctx-well-typed {.ρ'} (_ , PhiWFInductive {ρ'} Φ h1 h2) h3    | Inl refl   =
    tr
      (λ y → ∅ ⊢ fpaldef.expand y <= fpaldef.model-type y ==> fpaldef.splice-type y ==> fpaldef.expansion-type y)
      (fpaldef-inj (someinj (! (ctx-top ((Φ)₁) ρ' (FPalDef _) h1) · h3)))
      h2
  palctx-well-typed {ρ}   (_ , PhiWFInductive {ρ'} Φ h1 h2) h3    | Inr ne     = palctx-well-typed Φ (lem-neq-union-eq {Γ = π1 Φ} ne h3)
  palctx-well-typed {ρ}   (_ , PhiWFMac {ρ'} Φ h1) h3          with natEQ ρ ρ'
  palctx-well-typed {.ρ'} (_ , PhiWFMac {ρ'} Φ h1) h3             | Inl refl   = abort (paldef-mnotf (someinj (! (ctx-top (Φ ₁) ρ' (MPalDef _) h1) · h3)))
  palctx-well-typed {ρ}   (_ , PhiWFMac {ρ'} Φ h1) h3             | Inr ne     = palctx-well-typed Φ (lem-neq-union-eq {Γ = π1 Φ} ne h3)
