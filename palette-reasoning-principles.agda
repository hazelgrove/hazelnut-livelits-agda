open import Nat
open import Prelude
open import core
open import contexts
open import typed-palette-elaboration

module palette-reasoning-principles where
  palette-expansion-typing : ∀{Φ Γ ρ dm psplice esplice τsplice eexpanded expansion-type} →
                             Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> ((eexpanded ·: τsplice ==> expansion-type) ∘ esplice) ⇒ expansion-type →
                             Σ[ π ∈ paldef ] (Φ ρ == Some π × paldef.expansion-type π == expansion-type)
  palette-expansion-typing (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                             record
                               { expand = expand
                               ; model-type = model-type
                               ; expansion-type = expansion-type
                               } ,
                             x₂ , refl

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

  palette-splice-typing : ∀{Φ Γ ρ dm psplice esplice τsplice eexpanded expansion-type} →
                          Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> ((eexpanded ·: τsplice ==> expansion-type) ∘ esplice) ⇒ expansion-type →
                          Φ , Γ ⊢ psplice ~~> esplice ⇐ τsplice × Γ ⊢ esplice <= τsplice
  palette-splice-typing (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                          x₆ , typed-palette-elaboration-ana x₆

  palette-capture-avoidance : ∀{Φ Γ ρ dm psplice τsplice eresult expansion-type} →
                              Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ expansion-type →
                              Σ[ efun ∈ hexp ] Σ[ esplice ∈ hexp ] (eresult == efun ∘ esplice)
  palette-capture-avoidance {τsplice = τsplice}
                            (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} {eexpanded = eexpanded} {esplice = esplice} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                              (eexpanded ·: τsplice ==> expansion-type) , esplice , refl

  -- TODO assign betters name and move to a better place
  mutual
    -- singleton-with-EQ : ∀{x₁ x₂ τ} → ((■ (x₁ , τ)) x₂ | natEQ x₁ x₂) ≠ None
    -- singleton-with-EQ = ?

    fv-lemma-rff-ap : ∀{x e₁ e₂} → remove-from-free' x e₁ == [] → remove-from-free' x e₂ == [] → remove-from-free' x (e₁ ∘ e₂) == []
    fv-lemma-rff-ap x₁ x₂ = {!!}

    fv-lemma-rff : ∀{x e τ₁ τ₂} → (■ (x , τ₁)) ⊢ e => τ₂ → remove-from-free' x e == []
    fv-lemma-rff SConst = refl
    fv-lemma-rff (SAsc (ASubsume x₁ x₂)) = fv-lemma-rff x₁
    fv-lemma-rff (SAsc (ALam x₂ x₃ x₁)) = {!!}
    fv-lemma-rff (SVar x₂) = {!!}
    fv-lemma-rff (SAp x₁ x₂ x₃ (ASubsume x₄ x₅)) = {!!} -- fv-lemma-rff-ap (fv-lemma-rff x₄) (fv-lemma-rff x₂)
    fv-lemma-rff (SAp x₁ x₂ x₃ (ALam x₅ x₆ x₄)) = {!!}
    fv-lemma-rff SEHole = refl
    fv-lemma-rff (SNEHole x₁ x₂) = fv-lemma-rff x₂
    fv-lemma-rff (SLam x₂ x₁) = {!!}

    fv-lemma-ana : ∀{e τ} → ∅ ⊢ e <= τ → free-vars e == []
    fv-lemma-ana {c} _ = refl
    fv-lemma-ana {e ·: τ} (ASubsume (SAsc x) x₁) = fv-lemma-ana x
    fv-lemma-ana {X x} (ASubsume (SVar ()) x₂)
    fv-lemma-ana {·λ x e} (ASubsume () x₂)
    fv-lemma-ana {·λ x e} (ALam x₁ x₂ x₃) = {!!}
    fv-lemma-ana {·λ x [ τ ] e} (ASubsume (SLam x₁ x₃) x₂) = fv-lemma-rff x₃
    fv-lemma-ana {⦇⦈[ u ]} _ = refl
    fv-lemma-ana {⦇⌜ e ⌟⦈[ u ]} (ASubsume (SNEHole x x₂) x₁) = fv-lemma-ana (ASubsume x₂ TCHole2)
    fv-lemma-ana {e₁ ∘ e₂} (ASubsume (SAp x x₂ x₃ x₄) x₁) = {!!} -- (fv-lemma x₄) (fv-lemma)

  palette-context-independence : ∀{Φ Γ ρ dm psplice esplice τsplice efun expansion-type} →
                                 Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> efun ∘ esplice ⇒ expansion-type →
                                 free-vars efun == []
  palette-context-independence (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                                 fv-lemma-ana x₇
