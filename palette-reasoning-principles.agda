open import Nat
open import Prelude
open import List
open import core
open import contexts
open import typed-palette-elaboration

module palette-reasoning-principles where

  -- Some useful lemmas about free-vars and remove-from-free'. Not currently in core so as to reduce noise.
  mutual
    rff-lemma-ana : ∀{Γ x x' e τ₁ τ₂} → x # Γ → (Γ ,, (x' , τ₁)) ⊢ e <= τ₂ → x in-List remove-from-free' x' e → ⊥
    rff-lemma-ana {Γ} {x} {x'} {e} h₁ h₂ h₃ with   natEQ x x'
    rff-lemma-ana {Γ} {x} {x'} {e} h₁ h₂ h₃      | Inl x==x'  = remove-all-not-in natEQ (free-vars e) x' (tr ( λ y → y in-List remove-all natEQ (free-vars e) x') x==x' h₃)
    rff-lemma-ana {Γ} {x} {x'} {e} {τ₁} h₁ h₂ h₃ | Inr x≠x'   = a∉l→a∉remove-all-l-a' natEQ (fv-lemma-ana (lem-none-union {Γ = Γ} {τ₁} (flip x≠x') h₁) h₂) h₃

    rff-lemma-syn : ∀{Γ x x' e τ₁ τ₂} → x # Γ → (Γ ,, (x' , τ₁)) ⊢ e => τ₂ → x in-List remove-from-free' x' e → ⊥
    rff-lemma-syn {Γ} {x} {x'} {e} h₁ h₂ h₃ with   natEQ x x'
    rff-lemma-syn {Γ} {x} {x'} {e} h₁ h₂ h₃      | Inl x==x'  = remove-all-not-in natEQ (free-vars e) x' (tr ( λ y → y in-List remove-all natEQ (free-vars e) x') x==x' h₃)
    rff-lemma-syn {Γ} {x} {x'} {e} {τ₁} h₁ h₂ h₃ | Inr x≠x'   = a∉l→a∉remove-all-l-a' natEQ (fv-lemma-syn (lem-none-union {Γ = Γ} {τ₁} (flip x≠x') h₁) h₂) h₃

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


  record reasoning-principles (Φ : paldef ctx)
                              (Γ : tctx)
                              (ρ : Nat)
                              (dm : ihexp)
                              (τsplice : htyp)
                              (psplice : pexp)
                              (eresult : hexp)
                              (τresult : htyp) : Set where
    field
      π   : paldef
      πwf : Φ ρ == Some π --todo better name
      eexpanded : hexp
      esplice : hexp

      expanded-applicaiton-form : eresult == (eexpanded ·: τsplice ==> τresult) ∘ esplice
      expansion-typing          : (Γ ⊢ eresult => τresult) × (τresult == paldef.expansion-type π)
      responsibility            : Σ[ denc ∈ ihexp ] (((paldef.expand π) ∘ dm) ⇓ denc × denc ↑ eexpanded)
      splice-typing             : Φ , Γ ⊢ psplice ~~> esplice ⇐ τsplice × Γ ⊢ esplice <= τsplice
      context-independence      : free-vars (eexpanded ·: τsplice ==> τresult) == []

  -- All reasoning principles packaged into a single theorem
  all : ∀{Φ Γ ρ dm τsplice psplice eresult τresult} →
        Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
        reasoning-principles Φ Γ ρ dm τsplice psplice eresult τresult
  all h@(SPEApPal {dm = dm} {π} {denc} {eexpanded} {esplice = esplice} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
       record
         { π = π
         ; πwf = x₂
         ; eexpanded = eexpanded
         ; esplice = esplice
         ; expanded-applicaiton-form = refl
         ; expansion-typing = typed-palette-elaboration-synth h , refl
         ; responsibility = denc , x₄ , x₅
         ; splice-typing = x₆ , typed-palette-elaboration-ana x₆
         ; context-independence = ∅∈l→l==[] (λ x → fv-lemma-ana refl x₇)
         }
