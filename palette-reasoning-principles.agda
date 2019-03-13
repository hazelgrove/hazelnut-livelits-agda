open import Nat
open import Prelude
open import List
open import core
open import contexts
open import typed-palette-elaboration
open import lemmas-freevars

module palette-reasoning-principles where
  record reasoning-principles (Φ : palctx)
                              (Γ : tctx)
                              (ρ : Nat)
                              (dm : ihexp)
                              (τsplice : htyp)
                              (psplice : pexp)
                              (eresult : hexp)
                              (τresult : htyp) : Set where
    field
      π   : paldef
      domain : dom (Φ ₁) ρ
      eexpanded : hexp
      esplice : hexp

      expanded-application-form : eresult == (eexpanded ·: τsplice ==> τresult) ∘ esplice
      expansion-typing          : (Γ ⊢ eresult => τresult) × (τresult == paldef.expansion-type π)
      responsibility            : Σ[ denc ∈ ihexp ] (((paldef.expand π) ∘ dm) ⇓ denc × denc ↑ eexpanded) --todo: denc could be taken above with esplice etc if we want to
      splice-typing             : Φ , Γ ⊢ psplice ~~> esplice ⇐ τsplice × Γ ⊢ esplice <= τsplice
      context-independence      : free-vars (eexpanded ·: τsplice ==> τresult) == []

  palette-reasoning-principles : ∀{Φ Γ ρ dm τsplice psplice eresult τresult} →
        Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
        reasoning-principles Φ Γ ρ dm τsplice psplice eresult τresult
  palette-reasoning-principles h@(SPEApPal {dm = dm} {π} {denc} {eexpanded} {esplice = esplice} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
       record
         { π                         = π
         ; domain                    = _ , x₂
         ; eexpanded                 = eexpanded
         ; esplice                   = esplice
         ; expanded-application-form = refl
         ; expansion-typing          = typed-palette-elaboration-synth h , refl
         ; responsibility            = denc , x₄ , x₅
         ; splice-typing             = x₆ , typed-palette-elaboration-ana x₆
         ; context-independence      = ∅∈l→l==[] (λ x → fv-lemma-ana refl x₇)
         }
