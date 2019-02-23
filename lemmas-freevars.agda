open import Nat
open import Prelude
open import List
open import core
open import contexts


module lemmas-freevars where
  mutual
    -- todo: nick, in one sentence, what does this lemma show?
    rff-lemma-ana : ∀{Γ x x' e τ₁ τ₂} → x # Γ → (Γ ,, (x' , τ₁)) ⊢ e <= τ₂ → x in-List remove-from-free' x' e → ⊥
    rff-lemma-ana {Γ} {x} {x'} {e} h₁ h₂ h₃ with   natEQ x x'
    rff-lemma-ana {Γ} {x} {x'} {e} h₁ h₂ h₃      | Inl x==x'  = remove-all-not-in natEQ (free-vars e) x' (tr ( λ y → y in-List remove-all natEQ (free-vars e) x') x==x' h₃)
    rff-lemma-ana {Γ} {x} {x'} {e} {τ₁} h₁ h₂ h₃ | Inr x≠x'   = a∉l→a∉remove-all-l-a' natEQ (fv-lemma-ana (lem-none-union {Γ = Γ} {τ₁} (flip x≠x') h₁) h₂) h₃

    -- todo: ditto
    rff-lemma-syn : ∀{Γ x x' e τ₁ τ₂} → x # Γ → (Γ ,, (x' , τ₁)) ⊢ e => τ₂ → x in-List remove-from-free' x' e → ⊥
    rff-lemma-syn {Γ} {x} {x'} {e} h₁ h₂ h₃ with   natEQ x x'
    rff-lemma-syn {Γ} {x} {x'} {e} h₁ h₂ h₃      | Inl x==x'  = remove-all-not-in natEQ (free-vars e) x' (tr ( λ y → y in-List remove-all natEQ (free-vars e) x') x==x' h₃)
    rff-lemma-syn {Γ} {x} {x'} {e} {τ₁} h₁ h₂ h₃ | Inr x≠x'   = a∉l→a∉remove-all-l-a' natEQ (fv-lemma-syn (lem-none-union {Γ = Γ} {τ₁} (flip x≠x') h₁) h₂) h₃

    -- todo: ditto
    fv-lemma-ana : ∀{Γ x e τ} → x # Γ → Γ ⊢ e <= τ → x in-List (free-vars e) → ⊥
    fv-lemma-ana {Γ} {x} {c} h₁ h₂ ()
    fv-lemma-ana {Γ} {x} {e' ·: τ} h₁ (ASubsume h₂ _) h₃ = fv-lemma-syn h₁ h₂ h₃
    fv-lemma-ana {Γ} {x} {X x'} h₁ (ASubsume h₂ _) h₃ = fv-lemma-syn h₁ h₂ h₃
    fv-lemma-ana {Γ} {x} {·λ x' e'} h₁ (ASubsume () _) h₃
    fv-lemma-ana {Γ} {x} {·λ x' e'} hx (ALam hx' _ h₂) h₃ = rff-lemma-ana {Γ} hx h₂ h₃
    fv-lemma-ana {Γ} {x} {·λ x' [ τ ] e'} hx (ASubsume (SLam hx' h₂) _) h₃ = rff-lemma-syn {Γ} hx h₂ h₃
    fv-lemma-ana {Γ} {x} {⦇⦈[ u ]} h₁ h₂ ()
    fv-lemma-ana {Γ} {x} {⦇⌜ e' ⌟⦈[ u ]} h₁ (ASubsume (SNEHole _ h₂) _) h₃ = fv-lemma-syn h₁ h₂ h₃
    fv-lemma-ana {Γ} {x} {e₁ ∘ e₂} h₁ (ASubsume (SAp _ h₂ _ h₃) _) h₄ = not-in-append-comm natEQ (fv-lemma-syn h₁ h₂) (fv-lemma-ana h₁ h₃) h₄

    -- todo: ditto
    fv-lemma-syn : ∀{Γ x e τ} → x # Γ → Γ ⊢ e => τ → x in-List (free-vars e) → ⊥
    fv-lemma-syn {Γ} {x} {c} h₁ h₂ ()
    fv-lemma-syn {Γ} {x} {e' ·: τ} h₁ (SAsc h₂) h₃ = fv-lemma-ana h₁ h₂ h₃
    fv-lemma-syn {Γ} {.x'} {X x'} hx (SVar hx') InH = somenotnone (! hx' · hx)
    fv-lemma-syn {Γ} {x} {X x'} hx (SVar hx') (InT ())
    fv-lemma-syn {Γ} {x} {·λ x' e'} h₁ () h₃
    fv-lemma-syn {Γ} {x} {·λ x' [ τ ] e'} hx (SLam hx' h₂) h₃ = rff-lemma-syn {Γ} hx h₂ h₃
    fv-lemma-syn {Γ} {x} {⦇⦈[ u ]} h₁ h₂ ()
    fv-lemma-syn {Γ} {x} {⦇⌜ e' ⌟⦈[ u ]} h₁ (SNEHole _ h₂) h₃ = fv-lemma-syn h₁ h₂ h₃
    fv-lemma-syn {Γ} {x} {e₁ ∘ e₂} h₁ (SAp _ h₂ _ h₃) h₄ = not-in-append-comm natEQ (fv-lemma-syn h₁ h₂) (fv-lemma-ana h₁ h₃) h₄
