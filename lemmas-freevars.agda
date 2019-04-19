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
    fv-lemma-syn apt SConst ()
    fv-lemma-syn apt (SAsc x₁) = fv-lemma-ana apt x₁
    fv-lemma-syn apt (SVar x₂) InH = somenotnone (! x₂ · apt)
    fv-lemma-syn apt (SVar x₂) (InT ())
    fv-lemma-syn apt (SAp {e1 = e1} x₁ wt x₂ x₃) xin
      with inList++ {l1 = free-vars e1} natEQ xin
    ... | Inl x₄ = fv-lemma-syn apt wt x₄
    ... | Inr x₄ = fv-lemma-ana apt x₃ x₄
    fv-lemma-syn apt SEHole ()
    fv-lemma-syn apt (SNEHole x₁ wt) = fv-lemma-syn apt wt
    fv-lemma-syn {Γ} apt (SLam x₂ wt) xin = rff-lemma-syn {Γ} apt wt xin
    fv-lemma-syn apt (SFst wt x₁) = fv-lemma-syn apt wt
    fv-lemma-syn apt (SSnd wt x₁) = fv-lemma-syn apt wt
    fv-lemma-syn apt (SPair {e1 = e1} x₁ wt wt₁) xin
      with inList++ {l1 = free-vars e1} natEQ xin
    ... | Inl y = fv-lemma-syn apt wt y
    ... | Inr y = fv-lemma-syn apt wt₁ y
