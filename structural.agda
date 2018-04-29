open import Prelude
open import Nat
open import core
open import contexts

module structural where
  postulate
    weaken-ana-expand : ∀{ Γ e τ e' τ' Δ x τ* } →
                        -- todo: there's a freshness concern here; i'm
                        -- not sure if just being apart from Γ is good
                        -- enough. in POPL work it wasn't, we wanted
                        -- really aggressive freshness because of
                        -- barendrecht's
                        x # Γ →
                        Γ ⊢ e ⇐ τ ~> e' :: τ' ⊣ Δ →
                        (Γ ,, (x , τ*)) ⊢ e ⇐ τ ~> e' :: τ' ⊣ Δ
