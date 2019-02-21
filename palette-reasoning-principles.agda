open import Nat
open import Prelude
open import List
open import core
open import contexts
open import typed-palette-elaboration

-- If an `ap-pal` expression successfully expands, the following must hold:
module palette-reasoning-principles where
  -- The expansion result has a specific form; particularly that of a function application, where the function
  -- part is ascripted with an arrow type from the splice type (specified by the original expression) to the
  -- expansion result type.
  -- This form satisfies the `Capture Avoidance` principle described in "Reasonably Programmable Literal Notation",
  -- as it renders incorrect capturing structurally impossible.
  palette-application-form : ∀{Φ Γ ρ dm τsplice psplice eresult τresult} →
                             Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
                             Σ[ eexpanded ∈ hexp ] Σ[ esplice ∈ hexp ] (eresult == (eexpanded ·: τsplice ==> τresult) ∘ esplice)
  palette-application-form (SPEApPal {eexpanded = eexpanded} {esplice = esplice} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = eexpanded , esplice , refl

  -- The palette context contains a definition for the specified palette name.
  palette-context-lookup : ∀{Φ Γ ρ dm τsplice psplice eresult τresult} →
                           Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
                           Σ[ π ∈ paldef ] (Φ ρ == Some π)
  palette-context-lookup (SPEApPal {π = π} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = π , x₂

  -- The expanded expression synthesizes the result type (a consequence of the `Typed Palette Elaboration` theorem),
  -- and the result type is the same as the expansion type specified in the palette definition.
  palette-expansion-typing : ∀{Φ Γ ρ dm τsplice psplice eresult τresult π} →
                             Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
                             Φ ρ == Some π →
                             (Γ ⊢ eresult => τresult) × (τresult == paldef.expansion-type π)
  palette-expansion-typing h@(SPEApPal x x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₉ = typed-palette-elaboration-synth h , ap1 paldef.expansion-type (someinj (! x₃ · x₉))

  -- The model specified in the original expression has the type specified in the palette definition, and it does
  -- not rely on any bindings in the application site context.
  palette-model-typing : ∀{Φ Γ ρ dm τsplice psplice eresult τresult π} →
                         Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
                         Φ ρ == Some π →
                         ∅ , ∅ ⊢ dm :: paldef.model-type π
  palette-model-typing (SPEApPal {dm = dm} x x₂ x₃ x₄ x₅ x₆ x₇ x₈) x₁ = tr (λ y → ∅ , ∅ ⊢ dm :: paldef.model-type y) (someinj (! x₃ · x₁)) x₄

  -- The palette definition's `expand` function is responsible for expanding the model - the result of this expansion
  -- is evaluated to a value, then that value is decoded into an hexp
  palette-responsibility : ∀{Φ Γ ρ dm psplice τsplice eresult τresult eexpanded esplice π} →
                           Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
                           eresult == (eexpanded ·: τsplice ==> τresult) ∘ esplice →
                           Φ ρ == Some π →
                           Σ[ denc ∈ ihexp ] (((paldef.expand π) ∘ dm) ⇓ denc × denc ↑ eexpanded)
  palette-responsibility (SPEApPal {dm = dm} {denc = denc} x x₃ x₄ x₅ x₆ x₇ x₈ x₉) refl x₂ = denc , tr (λ y → Σ ((paldef.expand y ∘ dm) ↦* denc) (λ _ → denc final)) (someinj (! x₄ · x₂)) x₆ , x₇

  -- The splice expression expands into the argument part of the expanded form, which can be analyzed against the type
  -- specified by the original expression
  palette-splice-typing : ∀{Φ Γ ρ dm psplice τsplice eresult τresult eexpanded esplice} →
                          Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
                          eresult == (eexpanded ·: τsplice ==> τresult) ∘ esplice →
                          Φ , Γ ⊢ psplice ~~> esplice ⇐ τsplice × Γ ⊢ esplice <= τsplice
  palette-splice-typing (SPEApPal x x₂ x₃ x₄ x₅ x₆ x₇ x₈) refl = x₇ , typed-palette-elaboration-ana x₇

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

  -- The function part of the expanded form has no free variables, guaranteeing that it does not rely on any bindings in the application site context
  palette-context-independence : ∀{Φ Γ ρ dm psplice τsplice eresult τresult eexpanded esplice} →
                                 Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
                                 eresult == (eexpanded ·: τsplice ==> τresult) ∘ esplice →
                                 free-vars (eexpanded ·: τsplice ==> τresult) == []
  palette-context-independence (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} {eexpanded = eexpanded} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) refl =
                                 ∅∈l→l==[] (λ x → fv-lemma-ana refl x₇)
