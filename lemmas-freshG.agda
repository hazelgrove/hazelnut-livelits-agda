open import Prelude
open import core
open import contexts

module lemmas-freshG where
  -- the def above buries the sort of obvious pattern matching we'd like to
  -- do on the freshness in the conclusion, so we need lemmas that extract
  -- it for each constructor
  freshΓ-asc : {A : Set} → {Γ : A ctx} → ∀{e τ} → freshΓ Γ (e ·: τ) → freshΓ Γ e
  freshΓ-asc fr x x₁ with fr x x₁
  freshΓ-asc fr x x₁ | FRHAsc qq = qq

  freshΓ-ap1 : {A : Set} → {Γ : A ctx} → ∀{e1 e2} → freshΓ Γ (e1 ∘ e2) → freshΓ Γ e1
  freshΓ-ap1 fr x y with fr x y
  freshΓ-ap1 fr x y | FRHAp qq qq₁ = qq

  freshΓ-ap2 : {A : Set} → {Γ : A ctx} → ∀{e1 e2} → freshΓ Γ (e1 ∘ e2) → freshΓ Γ e2
  freshΓ-ap2 fr x y with fr x y
  freshΓ-ap2 fr x y | FRHAp qq qq₁ = qq₁

  freshΓ-nehole : {A : Set} → {Γ : A ctx} → ∀{e u} → freshΓ Γ (⦇⌜ e ⌟⦈[ u ]) → freshΓ Γ e
  freshΓ-nehole fr x y with fr x y
  freshΓ-nehole fr x y | FRHNEHole qq = qq

  freshΓ-lam1 : {A : Set} → {Γ : A ctx} → ∀{e x} → freshΓ Γ (·λ x e) → freshΓ Γ e
  freshΓ-lam1 fr x y with fr x y
  freshΓ-lam1 fr x y | FRHLam1 x₂ qq = qq

  freshΓ-lam2 : {A : Set} → {Γ : A ctx} → ∀{e τ x} → freshΓ Γ (·λ_[_]_ x τ e) → freshΓ Γ e
  freshΓ-lam2 fr x y with fr x y
  freshΓ-lam2 fr x y | FRHLam2 x₂ qq = qq

  lem-fresh-lam1 : ∀{x e} → freshh x (·λ x e) → ⊥
  lem-fresh-lam1 (FRHLam1 x₁ f) = x₁ refl

  lem-fresh-lam2 : ∀{x τ e} → freshh x (·λ x [ τ ] e) → ⊥
  lem-fresh-lam2 (FRHLam2 x₁ f) = x₁ refl
