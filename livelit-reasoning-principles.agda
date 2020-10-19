open import Nat
open import Prelude
open import List
open import core
open import contexts
open import typed-livelit-elaboration
open import lemmas-freevars

module livelit-reasoning-principles where
  record reasoning-principles (Φ : palctx)
                              (Γ : tctx)
                              (ρ : Nat)
                              (dm : iexp)
                              (τsplice : typ)
                              (êsplice : uexp)
                              (eresult : eexp)
                              (τresult : typ) : Set where
    field
      π   : livelitdef
      domain : dom (Φ ₁) ρ
      eexpanded : eexp
      esplice : eexp

      expanded-application-form : eresult == (eexpanded ·: τsplice ==> τresult) ∘ esplice
      expansion-typing          : (Γ ⊢ eresult => τresult) × (τresult == livelitdef.expansion-type π)
      responsibility            : Σ[ denc ∈ iexp ] (((livelitdef.expand π) ∘ dm) ⇓ denc × denc ↑ eexpanded) --todo: denc could be taken above with esplice etc if we want to
      splice-typing             : Φ , Γ ⊢ êsplice ~~> esplice ⇐ τsplice × Γ ⊢ esplice <= τsplice
      context-independence      : free-vars (eexpanded ·: τsplice ==> τresult) == []

  livelit-reasoning-principles : ∀{Φ Γ ρ dm τsplice psplice eresult τresult} →
        Φ , Γ ⊢ ap-pal ρ dm (τsplice , psplice) ~~> eresult ⇒ τresult →
        reasoning-principles Φ Γ ρ dm τsplice psplice eresult τresult
  livelit-reasoning-principles h@(SPEApPal {dm = dm} {π} {denc} {eexpanded} {esplice = esplice} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
       record
         { π                         = π
         ; domain                    = _ , x₂
         ; eexpanded                 = eexpanded
         ; esplice                   = esplice
         ; expanded-application-form = refl
         ; expansion-typing          = typed-livelit-elaboration-synth h , refl
         ; responsibility            = denc , x₄ , x₅
         ; splice-typing             = x₆ , typed-livelit-elaboration-ana x₆
         ; context-independence      = ∅∈l→l==[] (λ x → fv-lemma-ana refl x₇)
         }
