open import Nat
open import Prelude
open import core
open import contexts

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
  palette-responsibility (SPEApPal {π = record { expand = expand ; model-type = model-type ; expansion-type = expansion-type }} {denc = denc} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
                           record
                             { expand = expand
                             ; model-type = model-type
                             ; expansion-type = expansion-type
                             } ,
                           denc , x₂ , x₄ , x₅
