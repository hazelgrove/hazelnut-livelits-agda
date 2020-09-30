open import Nat
open import Prelude
open import core
open import contexts

module livelits-checks where
  -- in a well-formed livelit context, the `expand` of all definitions
  -- analyzes against the proper type
  llctx-well-typed : ∀{ρ π} →
                       (Φ : palctx) →
                       (ρ , FPalDef π) ∈ (Φ)₁ →
                       ∅ ⊢ fpaldef.expand π <= fpaldef.model-type π ==> fpaldef.splice-type π ==> fpaldef.expansion-type π
  llctx-well-typed (_ , PhiWFEmpty) ()
  llctx-well-typed {ρ}   (_ , PhiWFInductive {ρ'} Φ h1 h2) h3 with natEQ ρ ρ'
  llctx-well-typed {.ρ'} (_ , PhiWFInductive {ρ'} Φ h1 h2) h3    | Inl refl  with someinj (! (ctx-top ((Φ)₁) ρ' (FPalDef _) h1) · h3)
  llctx-well-typed {.ρ'} (_ , PhiWFInductive {ρ'} Φ h1 h2) h3 | Inl refl | refl = h2
  llctx-well-typed {ρ}   (_ , PhiWFInductive {ρ'} Φ h1 h2) h3    | Inr ne     = llctx-well-typed Φ (lem-neq-union-eq {Γ = π1 Φ} ne h3)
  llctx-well-typed {ρ}   (_ , PhiWFMac {ρ'} Φ h1) h3          with natEQ ρ ρ'
  llctx-well-typed {.ρ'} (_ , PhiWFMac {ρ'} Φ h1) h3             | Inl refl   with (! (ctx-top (Φ ₁) ρ' (MPalDef _) h1) · h3)
  llctx-well-typed {.ρ'} (_ , PhiWFMac {ρ'} Φ h1) h3 | Inl refl  | ()
  llctx-well-typed {ρ}   (_ , PhiWFMac {ρ'} Φ h1) h3             | Inr ne     = llctx-well-typed Φ (lem-neq-union-eq {Γ = π1 Φ} ne h3)
