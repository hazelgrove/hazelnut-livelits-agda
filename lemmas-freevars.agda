open import Nat
open import Prelude
open import List
open import core
open import contexts


module lemmas-freevars where
  mutual
    -- if e successfully type-checks via analysis, under a context which
    -- can only bind x in the final position, then the free vars of e, with
    -- the context's last binder removed, cannot contain x.
    rff-lemma-ana : ∀{Γ x x' e τ₁ τ₂} → x # Γ → (Γ ,, (x' , τ₁)) ⊢ e <= τ₂ → x inList remove-from-free' x' e → ⊥
    rff-lemma-ana {_} {x} {x'} {e} h₁ h₂ h₃ with   natEQ x x'
    rff-lemma-ana {Γ} {x} {x'} {e} h₁ h₂ h₃      | Inl x==x'  = remove-all-not-in natEQ (free-vars e) x' (tr ( λ y → y inList remove-all natEQ (free-vars e) x') x==x' h₃)
    rff-lemma-ana {Γ} {x} {x'} {e} {τ₁} h₁ h₂ h₃ | Inr x≠x'   = a∉l→a∉remove-all-l-a' natEQ (fv-lemma-ana (lem-none-union {Γ = Γ} {τ₁} (flip x≠x') h₁) h₂) h₃

    -- as above
    rff-lemma-syn : ∀{Γ x x' e τ₁ τ₂} → x # Γ → (Γ ,, (x' , τ₁)) ⊢ e => τ₂ → x inList remove-from-free' x' e → ⊥
    rff-lemma-syn {Γ} {x} {x'} {e} h₁ h₂ h₃ with   natEQ x x'
    rff-lemma-syn {Γ} {x} {x'} {e} h₁ h₂ h₃      | Inl x==x'  = remove-all-not-in natEQ (free-vars e) x' (tr ( λ y → y inList remove-all natEQ (free-vars e) x') x==x' h₃)
    rff-lemma-syn {Γ} {x} {x'} {e} {τ₁} h₁ h₂ h₃ | Inr x≠x'   = a∉l→a∉remove-all-l-a' natEQ (fv-lemma-syn (lem-none-union {Γ = Γ} {τ₁} (flip x≠x') h₁) h₂) h₃

    -- if e analysizes against type under a context that doesn't mention x,
    -- x is not in free vars of e
    fv-lemma-ana : ∀{Γ x e τ} → x # Γ → Γ ⊢ e <= τ → x inList (free-vars e) → ⊥
    fv-lemma-ana h₁ (ASubsume x₁ x₂) = fv-lemma-syn h₁ x₁
    fv-lemma-ana {Γ} h₁ (ALam x₂ x₃ h₂) = rff-lemma-ana {Γ} h₁ h₂

    -- if e synthesizes a type under a context that doesn't mention x, x is
    -- not in free vars of e
    fv-lemma-syn : ∀{Γ x e τ} → x # Γ → Γ ⊢ e => τ → x inList (free-vars e) → ⊥
    fv-lemma-syn {e = c} h₁ h₂ ()
    fv-lemma-syn {e = _ ·: _} h₁ (SAsc h₂) = fv-lemma-ana h₁ h₂
    fv-lemma-syn {e = X _} hx (SVar hx') InH = somenotnone (! hx' · hx)
    fv-lemma-syn {e = X _} hx (SVar hx') (InT ())
    fv-lemma-syn {e = ·λ _ _} h₁ ()
    fv-lemma-syn {Γ} {_} {·λ _ [ _ ] _} hx (SLam hx' h₂) = rff-lemma-syn {Γ} hx h₂
    fv-lemma-syn {e = ⦇⦈[ u ]} h₁ h₂ ()
    fv-lemma-syn {e = ⦇⌜ _ ⌟⦈[ _ ]} h₁ (SNEHole _ h₂) = fv-lemma-syn h₁ h₂
    fv-lemma-syn {e = e1 ∘ e2} h₁ (SAp _ h₂ _ h₃) inlist with inList++ {l1 = free-vars e1} natEQ inlist
    fv-lemma-syn {e = e1 ∘ e2} h₁ (SAp _ h₂ _ h₃) inlist | Inl x₁ = fv-lemma-syn h₁ h₂ x₁
    fv-lemma-syn {e = e1 ∘ e2} h₁ (SAp _ h₂ _ h₃) inlist | Inr x₁ = fv-lemma-ana h₁ h₃ x₁
    fv-lemma-syn {e = ⟨ e1 , e2 ⟩} h1 (SPair x₁ wt wt₁) inlist with inList++ {l1 = free-vars e1} natEQ inlist
    fv-lemma-syn {x = x} {⟨ _ , _ ⟩} h1 (SPair x₁ wt wt₁) inlist | Inl x₄ = fv-lemma-syn h1 wt x₄
    fv-lemma-syn {x = _} {⟨ _ , _ ⟩} h1 (SPair x₁ wt wt₁) inlist | Inr x₄ = fv-lemma-syn h1 wt₁ x₄
    fv-lemma-syn {e = fst _} h1 (SFst wt x₁) = fv-lemma-syn h1 wt
    fv-lemma-syn {e = snd _} h1 (SSnd wt x₁) = fv-lemma-syn h1 wt
