open import Nat
open import Prelude
open import List
open import core
open import contexts
open import typed-expansion
open import lemmas-freevars

module livelit-reasoning-principles where
  record reasoning-principles (Φ : livelitctx)
                              (Γ : tctx)
                              (a : livelitname)
                              (dm : iexp)
                              (τsplice : typ)
                              (êsplice : uexp)
                              (eresult : eexp)
                              (τresult : typ) : Set where
    field
      π   : livelitdef
      domain : dom (Φ ₁) a
      eexpanded : eexp
      esplice : eexp

      expanded-application-form : eresult == (eexpanded ·: τsplice ==> τresult) ∘ esplice
      expansion-typing          : (Γ ⊢ eresult => τresult) × (τresult == livelitdef.expansion-type π)
      responsibility            : Σ[ denc ∈ iexp ] (((livelitdef.expand π) ∘ dm) ⇓ denc × denc ↑ eexpanded)
      splice-typing             : Φ , Γ ⊢ êsplice ~~> esplice ⇐ τsplice × Γ ⊢ esplice <= τsplice
      context-independence      : free-vars (eexpanded ·: τsplice ==> τresult) == []

  livelit-reasoning-principles : ∀{Φ Γ a dm τsplice psplice eresult τresult u} →
        Φ , Γ ⊢ ＄ a ⟨ dm ⁏ (τsplice , psplice) :: [] ⟩[ u ] ~~> eresult ⇒ τresult →
        reasoning-principles Φ Γ a dm τsplice psplice eresult τresult
  livelit-reasoning-principles h@(SPEApLivelit {dm = dm} {π} {denc} {eexpanded} {esplice = esplice} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
       record
         { π                         = π
         ; domain                    = _ , x₂
         ; eexpanded                 = eexpanded
         ; esplice                   = esplice
         ; expanded-application-form = refl
         ; expansion-typing          = typed-expansion-synth h , refl
         ; responsibility            = denc , x₄ , x₅
         ; splice-typing             = x₆ , typed-expansion-ana x₆
         ; context-independence      = ∅∈l→l==[] (λ x → fv-lemma-ana refl x₇)
         }
