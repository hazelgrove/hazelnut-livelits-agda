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
  mutual
    weaken-synth : ∀{ x Γ e τ τ'} → freshh x e
                                  → Γ ⊢ e => τ
                                  → (Γ ,, (x , τ')) ⊢ e => τ
    weaken-synth FRHConst SConst = SConst
    weaken-synth (FRHAsc frsh) (SAsc x₁) = SAsc (weaken-ana frsh x₁)
    weaken-synth {Γ = Γ} (FRHVar {x = x} x₁) (SVar {x = y} x₂) = SVar (x∈∪l Γ (■(x , _)) y _  x₂)
    weaken-synth {Γ = Γ} (FRHLam2 x₁ frsh) (SLam x₂ wt) =
                    SLam (apart-extend1 Γ (flip x₁) x₂)
                         (exchange-synth {Γ = Γ} (flip x₁) ((weaken-synth frsh wt)))
    weaken-synth FRHEHole SEHole = SEHole
    weaken-synth (FRHNEHole frsh) (SNEHole x₁ wt) = SNEHole x₁ (weaken-synth frsh wt)
    weaken-synth (FRHAp frsh frsh₁) (SAp x₁ wt x₂ x₃) = SAp x₁ (weaken-synth frsh wt) x₂ (weaken-ana frsh₁ x₃)

    weaken-ana : ∀{x Γ e τ τ'} → freshh x e
                               → Γ ⊢ e <= τ
                               → (Γ ,, (x , τ')) ⊢ e <= τ
    weaken-ana frsh (ASubsume x₁ x₂) = ASubsume (weaken-synth frsh x₁) x₂
    weaken-ana {Γ = Γ} (FRHLam1 neq frsh) (ALam x₂ x₃ wt) =
                     ALam (apart-extend1 Γ (flip neq) x₂)
                          x₃
                          (exchange-ana {Γ = Γ} (flip neq) (weaken-ana frsh wt))

  -- a context Γ is fresh if it only has bindings for variables that are fresh in e
  freshΓ : {A : Set} → (Γ : A ctx) → (e : hexp) → Set
  freshΓ {A} Γ e = (x : Nat) → dom Γ x → freshh x e

  freshΓ-asc : {A : Set} → {Γ : A ctx} → ∀{e τ} → freshΓ Γ (e ·: τ) → freshΓ Γ e
  freshΓ-asc fr x x₁ with fr x x₁
  freshΓ-asc fr x x₁ | FRHAsc qq = qq

  mutual
    weaken-synth-closed : ∀{e τ Γ} → freshΓ Γ e → ∅ ⊢ e => τ → Γ ⊢ e => τ
    weaken-synth-closed frsh SConst = SConst
    weaken-synth-closed frsh (SAsc x) = SAsc (weaken-ana-closed (freshΓ-asc frsh) x)
    weaken-synth-closed frsh (SVar x₁) = abort (somenotnone (! x₁))
    weaken-synth-closed frsh (SAp x wt x₁ x₂) = SAp x (weaken-synth-closed {!!} wt) x₁ (weaken-ana-closed {!!} x₂)
    weaken-synth-closed frsh SEHole = SEHole
    weaken-synth-closed frsh (SNEHole x wt) = SNEHole x (weaken-synth-closed {!!} wt)
    weaken-synth-closed frsh (SLam x₁ wt) = SLam {!!} {!!}

    weaken-ana-closed : ∀{e τ Γ} → freshΓ Γ e →  ∅ ⊢ e <= τ → Γ ⊢ e <= τ
    weaken-ana-closed frsh (ASubsume x x₁) = ASubsume (weaken-synth-closed {!!} x) x₁
    weaken-ana-closed frsh (ALam x₁ x₂ wt) = ALam {!!} x₂ {!!}

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
