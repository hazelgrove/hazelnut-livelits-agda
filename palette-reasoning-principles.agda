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
    rff-lemma-ap : ∀{x} (e₁ e₂ : hexp) → remove-from-free' x e₁ == [] → remove-from-free' x e₂ == [] → remove-from-free' x (e₁ ∘ e₂) == []
    rff-lemma-ap {x} e₁ e₂ h₀ h₁ with free-vars e₁ | free-vars e₂
    rff-lemma-ap {x} e₁ e₂ h₁ h₂    | fv-e₁        | fv-e₂        =
      ! (filter-append-comm (natneqb' x) fv-e₁ fv-e₂) ·
      tr (λ y → y ++ filter (natneqb' x) fv-e₂ == []) (! h₁) (tr (λ y → [] ++ y == []) (! h₂) refl)

    rff-lemma-ana : ∀{x e τ₁ τ₂} → (■ (x , τ₁)) ⊢ e <= τ₂ → remove-from-free' x e == []
    rff-lemma-ana (ASubsume x₁ x₂) = rff-lemma-syn x₁
    rff-lemma-ana (ALam x₂ x₃ x₁) = {!!}

    rff-lemma-syn : ∀{x e τ₁ τ₂} → (■ (x , τ₁)) ⊢ e => τ₂ → remove-from-free' x e == []
    rff-lemma-syn SConst = refl
    rff-lemma-syn (SAsc x) = rff-lemma-ana x
    rff-lemma-syn {x} (SVar {x = x'} _) with natEQ x x'
    rff-lemma-syn {x} (SVar {x = x'} _)    | Inl refl   = refl
    rff-lemma-syn {x} (SVar {x = x'} ())   | Inr f
    rff-lemma-syn (SAp {e1 = e₁} {e2 = e₂} x₁ x₂ x₃ x₄) = rff-lemma-ap e₁ e₂ (rff-lemma-syn x₂) (rff-lemma-ana x₄)
    rff-lemma-syn SEHole = refl
    rff-lemma-syn (SNEHole x₁ x₂) = rff-lemma-syn x₂
    rff-lemma-syn (SLam x₂ x₁) = {!!}

    fv-lemma-ap : (e₁ e₂ : hexp) → free-vars e₁ == [] → free-vars e₂ == [] → (free-vars e₁ ++ free-vars e₂) == []
    fv-lemma-ap e₁ e₂ x x₁ with free-vars e₁ | free-vars e₂
    fv-lemma-ap e₁ e₂ x x₁    | []           | []           = refl
    fv-lemma-ap e₁ e₂ () x₁   | _ :: _       | []
    fv-lemma-ap e₁ e₂ x ()    | _            | _ :: _

    fv-lemma-ana : ∀{e τ} → ∅ ⊢ e <= τ → free-vars e == []
    fv-lemma-ana {c} _ = refl
    fv-lemma-ana {e ·: τ} (ASubsume (SAsc x) x₁) = fv-lemma-ana x
    fv-lemma-ana {X x} (ASubsume (SVar ()) x₂)
    fv-lemma-ana {·λ x e} (ASubsume () x₂)
    fv-lemma-ana {·λ x e} (ALam x₁ x₂ x₃) = rff-lemma-ana x₃
    fv-lemma-ana {·λ x [ τ ] e} (ASubsume (SLam x₁ x₃) x₂) = rff-lemma-syn x₃
    fv-lemma-ana {⦇⦈[ u ]} _ = refl
    fv-lemma-ana {⦇⌜ e ⌟⦈[ u ]} (ASubsume (SNEHole x x₂) x₁) = fv-lemma-ana (ASubsume x₂ TCHole2)
    fv-lemma-ana {e₁ ∘ e₂} (ASubsume (SAp x x₂ x₃ x₄) x₁) = fv-lemma-ap e₁ e₂ (fv-lemma-syn x₂) (fv-lemma-ana x₄)

    fv-lemma-syn : ∀{e τ} → ∅ ⊢ e => τ → free-vars e == []
    fv-lemma-syn SConst = refl
    fv-lemma-syn (SAsc x) = fv-lemma-ana x
    fv-lemma-syn (SVar ())
    fv-lemma-syn {e₁ ∘ e₂} (SAp x x₁ x₂ x₃) = fv-lemma-ap e₁ e₂ (fv-lemma-syn x₁) (fv-lemma-ana x₃)
    fv-lemma-syn SEHole = refl
    fv-lemma-syn (SNEHole x x₁) = fv-lemma-syn x₁
    fv-lemma-syn (SLam x₁ x) = rff-lemma-syn x

  palette-context-independence : ∀{Φ Γ ρ dm psplice esplice τsplice efun expansion-type} →
                                 Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> efun ∘ esplice ⇒ expansion-type →
                                 free-vars efun == []
  palette-context-independence (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                                 fv-lemma-ana x₇
