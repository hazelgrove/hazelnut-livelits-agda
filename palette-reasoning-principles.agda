open import Nat
open import Prelude
open import List
open import core
open import contexts
open import typed-palette-elaboration

-- If an `ap-pal` expression successfully expands, the following must hold:
module palette-reasoning-principles where
  -- The expanded expression has a specific form, which is useful for characterizing the remaining reasoning principles
  palette-expanded-form : ∀{Φ Γ ρ dm τsplice psplice eresult expansion-type} →
                          Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ expansion-type →
                          Σ[ eexpanded ∈ hexp ] Σ[ esplice ∈ hexp ] (eresult == (eexpanded ·: τsplice ==> expansion-type) ∘ esplice)
  palette-expanded-form (SPEApPal {eexpanded = eexpanded} {esplice = esplice} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = eexpanded , esplice , refl

  -- The expanded expression synthesizes the expansion type specified in the palette definition
  palette-expansion-typing : ∀{Φ Γ ρ dm psplice esplice τsplice eexpanded expansion-type} →
                             Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> (eexpanded ·: τsplice ==> expansion-type) ∘ esplice ⇒ expansion-type →
                             Σ[ π ∈ paldef ] (Φ ρ == Some π × paldef.expansion-type π == expansion-type)
  palette-expansion-typing (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                             record
                               { expand = expand
                               ; model-type = model-type
                               ; expansion-type = expansion-type
                               } ,
                             x₂ , refl

  -- The palette definition's `expand` function is responsible for expanding the model - the result of this expansion is evaluated to a value, then that value is decoded into an hexp
  palette-responsibility : ∀{Φ Γ ρ dm psplice esplice τsplice eexpanded expansion-type} →
                           Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> ((eexpanded ·: τsplice ==> expansion-type) ∘ esplice) ⇒ expansion-type →
                           Σ[ π ∈ paldef ] Σ[ denc ∈ ihexp ] (Φ ρ == Some π × ((paldef.expand π) ∘ dm) ⇓ denc × denc ↑ eexpanded)
  palette-responsibility (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} {denc} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                           record
                             { expand = expand
                             ; model-type = model-type
                             ; expansion-type = expansion-type
                             } ,
                           denc , x₂ , x₄ , x₅

  -- The splice expression will also expand successfully, and the result can be analyzed against the type specified by the `ap-pal` expression
  palette-splice-typing : ∀{Φ Γ ρ dm psplice esplice τsplice eexpanded expansion-type} →
                          Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> ((eexpanded ·: τsplice ==> expansion-type) ∘ esplice) ⇒ expansion-type →
                          Φ , Γ ⊢ psplice ~~> esplice ⇐ τsplice × Γ ⊢ esplice <= τsplice
  palette-splice-typing (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                          x₆ , typed-palette-elaboration-ana x₆

  -- TODO assign betters name and move to a better place
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

  -- The function component of the expanded form has no free variables, guaranteeing that it does not rely on any bindings in the application site context
  palette-context-independence : ∀{Φ Γ ρ dm psplice esplice τsplice eexpanded expansion-type} →
                                 Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> ((eexpanded ·: τsplice ==> expansion-type) ∘ esplice) ⇒ expansion-type →
                                 free-vars (eexpanded ·: τsplice ==> expansion-type) == []
  palette-context-independence (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} {eexpanded = eexpanded} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                                 ∅∈l→l==[] (λ x → fv-lemma-ana refl x₇)
