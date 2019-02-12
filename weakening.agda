open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-disjointness
open import exchange

-- this module contains all the proofs of different weakening structural
-- properties that we use for the hypothetical judgements
module weakening where
  mutual
    weaken-subst-Δ : ∀{Δ1 Δ2 Γ σ Γ'} → Δ1 ## Δ2
                                     → Δ1 , Γ ⊢ σ :s: Γ'
                                     → (Δ1 ∪ Δ2) , Γ ⊢ σ :s: Γ'
    weaken-subst-Δ disj (STAId x) = STAId x
    weaken-subst-Δ disj (STASubst subst x) = STASubst (weaken-subst-Δ disj subst) (weaken-ta-Δ1 disj x)

    weaken-ta-Δ1 : ∀{Δ1 Δ2 Γ d τ} → Δ1 ## Δ2
                                  → Δ1 , Γ ⊢ d :: τ
                                  → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
    weaken-ta-Δ1 disj TAConst = TAConst
    weaken-ta-Δ1 disj (TAVar x₁) = TAVar x₁
    weaken-ta-Δ1 disj (TALam x₁ wt) = TALam x₁ (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TAAp wt wt₁) = TAAp (weaken-ta-Δ1 disj wt) (weaken-ta-Δ1 disj wt₁)
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TAEHole {u = u} {Γ' = Γ'} x x₁) = TAEHole (x∈∪l Δ1 Δ2 u _ x ) (weaken-subst-Δ disj x₁)
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TANEHole {Γ' = Γ'} {u = u} x wt x₁) = TANEHole (x∈∪l Δ1 Δ2 u _ x) (weaken-ta-Δ1 disj wt) (weaken-subst-Δ disj x₁)
    weaken-ta-Δ1 disj (TACast wt x) = TACast (weaken-ta-Δ1 disj wt) x
    weaken-ta-Δ1 disj (TAFailedCast wt x x₁ x₂) = TAFailedCast (weaken-ta-Δ1 disj wt) x x₁ x₂

  -- this is a little bit of a time saver. since ∪ is commutative on
  -- disjoint contexts, and we need that premise anyway in both positions,
  -- there's no real reason to repeat the inductive argument above
  weaken-ta-Δ2 : ∀{Δ1 Δ2 Γ d τ} → Δ1 ## Δ2
                                → Δ2 , Γ ⊢ d :: τ
                                → (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  weaken-ta-Δ2 {Δ1} {Δ2} {Γ} {d} {τ} disj D = tr (λ q → q , Γ ⊢ d :: τ) (∪comm Δ2 Δ1 (##-comm disj)) (weaken-ta-Δ1 (##-comm disj) D)


  -- note that these statements are somewhat stronger than usual. this is
  -- because we don't have implcit α-conversion. this reifies the
  -- often-silent on paper assumption that if you collide with a bound
  -- variable you can just α-convert it away and not worry.
  -- mutual
  --   weaken-synth : ∀{ x Γ e τ τ'} → freshh x e
  --                                 → Γ ⊢ e => τ
  --                                 → (Γ ,, (x , τ')) ⊢ e => τ
  --   weaken-synth FRHConst SConst = SConst
  --   weaken-synth (FRHAsc frsh) (SAsc x₁) = SAsc (weaken-ana frsh x₁)
  --   weaken-synth {Γ = Γ} (FRHVar {x = x} x₁) (SVar {x = y} x₂) = SVar (x∈∪l Γ (■(x , _)) y _  x₂)
  --   weaken-synth {Γ = Γ} (FRHLam2 x₁ frsh) (SLam x₂ wt) =
  --                   SLam (apart-extend1 Γ (flip x₁) x₂)
  --                        (exchange-synth {Γ = Γ} (flip x₁) ((weaken-synth frsh wt)))
  --   weaken-synth FRHEHole SEHole = SEHole
  --   weaken-synth (FRHNEHole frsh) (SNEHole x₁ wt) = SNEHole x₁ (weaken-synth frsh wt)
  --   weaken-synth (FRHAp frsh frsh₁) (SAp x₁ wt x₂ x₃) = SAp x₁ (weaken-synth frsh wt) x₂ (weaken-ana frsh₁ x₃)

  --   weaken-ana : ∀{x Γ e τ τ'} → freshh x e
  --                              → Γ ⊢ e <= τ
  --                              → (Γ ,, (x , τ')) ⊢ e <= τ
  --   weaken-ana frsh (ASubsume x₁ x₂) = ASubsume (weaken-synth frsh x₁) x₂
  --   weaken-ana {Γ = Γ} (FRHLam1 neq frsh) (ALam x₂ x₃ wt) =
  --                    ALam (apart-extend1 Γ (flip neq) x₂)
  --                         x₃
  --                         (exchange-ana {Γ = Γ} (flip neq) (weaken-ana frsh wt))

  -- todo move
  -- a context Γ is fresh if it only has bindings for variables that are fresh in e
  freshΓ : {A : Set} → (Γ : A ctx) → (e : hexp) → Set
  freshΓ {A} Γ e = (x : Nat) → dom Γ x → freshh x e

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

  -- todo move
  lem-reassoc : {A : Set} {Γ Γ' : A ctx} {x : Nat} {τ : A} → (x # Γ') → (Γ ,, (x , τ)) ∪ Γ' == (Γ ∪ Γ') ,, (x , τ)
  lem-reassoc {A} {Γ} {Γ'} {x} {τ} apt with lem-apart-sing-disj apt
  ... | disj = (∪assoc Γ (■ (x , τ)) Γ' disj) ·
                 (ap1 (λ qq → Γ ∪ qq) (∪comm (■ (x , τ)) (Γ') disj) ·
                   ! (∪assoc Γ Γ' (■ (x , τ)) (##-comm disj)))

  -- note that note that separately we've proven disjointness implies
  -- commutativity of ∪ so this is one transport away from the other
  -- possible statement of weakening with union. it's possible that only
  -- one of them needs the disjointness premise due to the asymmetry in defining ∪.
  mutual
    weaken-synth-∪ : ∀{e τ Γ Γ'} → Γ ## Γ' → freshΓ Γ' e → Γ ⊢ e => τ → (Γ ∪ Γ')  ⊢ e => τ
    weaken-synth-∪ disj frsh SConst = SConst
    weaken-synth-∪ disj frsh (SAsc x) = SAsc (weaken-ana-∪ disj (freshΓ-asc frsh) x)
    weaken-synth-∪ {Γ = Γ} {Γ' = Γ'} disj frsh (SVar {x = x} x₁) = SVar (x∈∪l Γ Γ' x _ x₁)
    weaken-synth-∪ disj frsh (SAp x wt x₁ x₂) = SAp x (weaken-synth-∪ disj (freshΓ-ap1 frsh) wt)
                                                      x₁
                                                      (weaken-ana-∪ disj (freshΓ-ap2 frsh) x₂)
    weaken-synth-∪ disj frsh SEHole = SEHole
    weaken-synth-∪ disj frsh (SNEHole x wt) = SNEHole x (weaken-synth-∪ disj (freshΓ-nehole frsh) wt)
    weaken-synth-∪ {Γ = Γ} {Γ' = Γ'} disj frsh (SLam {e = e} {τ2 = τ2} {x = x}  x₁ wt)
      with ctxindirect Γ' x
    ... | Inl qq = abort (lem-fresh-lam2 (frsh x qq))
    ... | Inr qq = SLam (apart-parts Γ Γ' x x₁ qq)
                             (tr (λ qq → qq ⊢ e => τ2) (lem-reassoc {Γ = Γ} qq)
                                                       (weaken-synth-∪ (disjoint-parts disj (lem-apart-sing-disj qq)) (freshΓ-lam2 frsh) wt))

    weaken-ana-∪ : ∀{e τ Γ Γ'} → Γ ## Γ' → freshΓ Γ' e →  Γ ⊢ e <= τ → (Γ ∪ Γ') ⊢ e <= τ
    weaken-ana-∪ disj frsh (ASubsume x x₁) = ASubsume (weaken-synth-∪ disj frsh x) x₁
    weaken-ana-∪ {Γ = Γ} {Γ' = Γ'} disj frsh (ALam {e = e} {τ2 = τ2} {x = x} x₁ x₂ wt)
      with ctxindirect Γ' x
    ... | Inl qq = abort (lem-fresh-lam1 (frsh x qq))
    ... | Inr qq = ALam (apart-parts Γ Γ' x x₁ qq)
                        x₂
                        (tr (λ qq → qq ⊢ e <= τ2) (lem-reassoc {Γ = Γ} qq)
                                                  (weaken-ana-∪ (disjoint-parts disj (lem-apart-sing-disj qq)) (freshΓ-lam1 frsh) wt))

  weaken-synth-closed : ∀{e τ Γ} → freshΓ Γ e → ∅ ⊢ e => τ → Γ ⊢ e => τ
  weaken-synth-closed {e} {τ} {Γ} f wt = tr (λ qq → qq ⊢ e => τ) ∅∪1 (weaken-synth-∪ (empty-disj _) f wt)

  weaken-ana-closed : ∀{e τ Γ} → freshΓ Γ e → ∅ ⊢ e <= τ → Γ ⊢ e <= τ
  weaken-ana-closed {e} {τ} {Γ} f wt = tr (λ qq → qq ⊢ e <= τ) ∅∪1 (weaken-ana-∪ (empty-disj _) f wt)

  -- todo: classic forms of weakening probably follow from the union version
  mutual
    fresh-apart-synth : ∀ {e τ x Γ} → Γ ⊢ e => τ → freshh x e → x # Γ
    fresh-apart-synth SConst FRHConst = {!!}
    fresh-apart-synth (SAsc x₁) (FRHAsc f) = {!!}
    fresh-apart-synth (SVar x₂) (FRHVar x₃) = {!!}
    fresh-apart-synth (SAp x₁ wt x₂ x₃) (FRHAp f f₁) = {!!}
    fresh-apart-synth SEHole FRHEHole = {!!}
    fresh-apart-synth (SNEHole x₁ wt) (FRHNEHole f) = {!!}
    fresh-apart-synth (SLam x₂ wt) (FRHLam2 x₃ f) = {!!}

    fresh-apart-ana : ∀ {e τ x Γ} → Γ ⊢ e <= τ → freshh x e → x # Γ
    fresh-apart-ana = {!!}

  weaken-synth : ∀{ x Γ e τ τ'} → freshh x e
                                  → Γ ⊢ e => τ
                                  → (Γ ,, (x , τ')) ⊢ e => τ
  weaken-synth f wt = weaken-synth-∪ {!!} {!!} wt

  weaken-ana : ∀{x Γ e τ τ'} → freshh x e
                               → Γ ⊢ e <= τ
                               → (Γ ,, (x , τ')) ⊢ e <= τ
  weaken-ana f wt = weaken-ana-∪ {!!} {!!} wt



  mutual
    weaken-subst-Γ : ∀{ x Γ Δ σ Γ' τ} →
                     envfresh x σ →
                     Δ , Γ ⊢ σ :s: Γ' →
                     Δ , (Γ ,, (x , τ)) ⊢ σ :s: Γ'
    weaken-subst-Γ {Γ = Γ} (EFId x₁) (STAId x₂) = STAId (λ x τ x₃ → x∈∪l Γ _ x τ (x₂ x τ x₃) )
    weaken-subst-Γ {x = x} {Γ = Γ} (EFSubst x₁ efrsh x₂) (STASubst {y = y} {τ = τ'} subst x₃) =
      STASubst (exchange-subst-Γ {Γ = Γ} (flip x₂) (weaken-subst-Γ {Γ = Γ ,, (y , τ')} efrsh subst))
               (weaken-ta x₁ x₃)

    weaken-ta : ∀{x Γ Δ d τ τ'} →
                fresh x d →
                Δ , Γ ⊢ d :: τ →
                Δ , Γ ,, (x , τ') ⊢ d :: τ
    weaken-ta _ TAConst = TAConst
    weaken-ta {x} {Γ} {_} {_} {τ} {τ'} (FVar x₂) (TAVar x₃) = TAVar (x∈∪l Γ (■ (x , τ')) _ _ x₃)
    weaken-ta {x = x} frsh (TALam {x = y} x₂ wt) with natEQ x y
    weaken-ta (FLam x₁ x₂) (TALam x₃ wt) | Inl refl = abort (x₁ refl)
    weaken-ta {Γ = Γ} {τ' = τ'} (FLam x₁ x₃) (TALam {x = y} x₄ wt) | Inr x₂ = TALam (apart-extend1 Γ (flip x₁) x₄) (exchange-ta-Γ {Γ = Γ} (flip x₁) (weaken-ta x₃ wt))
    weaken-ta (FAp frsh frsh₁) (TAAp wt wt₁) = TAAp (weaken-ta frsh wt) (weaken-ta frsh₁ wt₁)
    weaken-ta (FHole x₁) (TAEHole x₂ x₃) = TAEHole x₂ (weaken-subst-Γ x₁ x₃)
    weaken-ta (FNEHole x₁ frsh) (TANEHole x₂ wt x₃) = TANEHole x₂ (weaken-ta frsh wt) (weaken-subst-Γ x₁ x₃)
    weaken-ta (FCast frsh) (TACast wt x₁) = TACast (weaken-ta frsh wt) x₁
    weaken-ta (FFailedCast frsh) (TAFailedCast wt x₁ x₂ x₃) = TAFailedCast (weaken-ta frsh wt) x₁ x₂ x₃
