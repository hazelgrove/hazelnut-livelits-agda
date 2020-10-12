open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-disjointness
open import exchange
open import lemmas-freshG

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
    weaken-ta-Δ1 disj (TAFst wt) = TAFst (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TASnd wt) = TASnd (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TAPair wt wt₁) = TAPair (weaken-ta-Δ1 disj wt) (weaken-ta-Δ1 disj wt₁)

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

  -- used in both cases below, so factored into a lemma to save repeated code
  lem-reassoc : {A : Set} {Γ Γ' : A ctx} {x : Nat} {τ : A} → (x # Γ') → (Γ ,, (x , τ)) ∪ Γ' == (Γ ∪ Γ') ,, (x , τ)
  lem-reassoc {A} {Γ} {Γ'} {x} {τ} apt with lem-apart-sing-disj apt
  ... | disj = (∪assoc Γ (■ (x , τ)) Γ' disj) ·
                 (ap1 (λ qq → Γ ∪ qq) (∪comm (■ (x , τ)) (Γ') disj) ·
                   ! (∪assoc Γ Γ' (■ (x , τ)) (##-comm disj)))

  -- first we prove a general form of weakening, that you can add any
  -- context Γ as long as it's fresh with respect to e
  mutual
    weaken-synth-∪ : ∀{e τ Γ Γ'} → freshΓ Γ' e → Γ ⊢ e => τ → (Γ ∪ Γ')  ⊢ e => τ
    weaken-synth-∪ frsh SConst = SConst
    weaken-synth-∪ frsh (SAsc x) = SAsc (weaken-ana-∪ (freshΓ-asc frsh) x)
    weaken-synth-∪ {Γ = Γ} {Γ' = Γ'} frsh (SVar {x = x} x₁) = SVar (x∈∪l Γ Γ' x _ x₁)
    weaken-synth-∪ frsh (SAp x wt x₁ x₂) = SAp x (weaken-synth-∪ (freshΓ-ap1 frsh) wt)
                                                      x₁
                                                      (weaken-ana-∪ (freshΓ-ap2 frsh) x₂)
    weaken-synth-∪ frsh SEHole = SEHole
    weaken-synth-∪ frsh (SNEHole x wt) = SNEHole x (weaken-synth-∪ (freshΓ-nehole frsh) wt)
    weaken-synth-∪ {Γ = Γ} {Γ' = Γ'} frsh (SLam {e = e} {τ2 = τ2} {x = x}  x₁ wt)
      with ctxindirect Γ' x
    ... | Inl qq = abort (lem-fresh-lam2 (frsh x qq))
    ... | Inr qq = SLam (apart-parts Γ Γ' x x₁ qq)
                             (tr (λ qq → qq ⊢ e => τ2) (lem-reassoc {Γ = Γ} qq)
                                                       (weaken-synth-∪ (freshΓ-lam2 frsh) wt))
    weaken-synth-∪ frsh (SFst wt x) = SFst (weaken-synth-∪ (freshΓ-fst frsh) wt) x
    weaken-synth-∪ frsh (SSnd wt x) = SSnd (weaken-synth-∪ (freshΓ-snd frsh) wt) x
    weaken-synth-∪ frsh (SPair hd wt wt₁) = SPair hd (weaken-synth-∪ (freshΓ-pair1 frsh) wt) (weaken-synth-∪ (freshΓ-pair2 frsh) wt₁)

    weaken-ana-∪ : ∀{e τ Γ Γ'} → freshΓ Γ' e →  Γ ⊢ e <= τ → (Γ ∪ Γ') ⊢ e <= τ
    weaken-ana-∪ frsh (ASubsume x x₁) = ASubsume (weaken-synth-∪ frsh x) x₁
    weaken-ana-∪ {Γ = Γ} {Γ' = Γ'} frsh (ALam {e = e} {τ2 = τ2} {x = x} x₁ x₂ wt)
      with ctxindirect Γ' x
    ... | Inl qq = abort (lem-fresh-lam1 (frsh x qq))
    ... | Inr qq = ALam (apart-parts Γ Γ' x x₁ qq)
                        x₂
                        (tr (λ qq → qq ⊢ e <= τ2) (lem-reassoc {Γ = Γ} qq)
                                                  (weaken-ana-∪ (freshΓ-lam1 frsh) wt))

  -- it follows from this that if the term is closed, you can weaken with
  -- any context that's fresh in e
  weaken-synth-closed : ∀{e τ Γ} → freshΓ Γ e → ∅ ⊢ e => τ → Γ ⊢ e => τ
  weaken-synth-closed {e} {τ} {Γ} f wt = tr (λ qq → qq ⊢ e => τ) ∅∪1 (weaken-synth-∪ f wt)

  weaken-ana-closed : ∀{e τ Γ} → freshΓ Γ e → ∅ ⊢ e <= τ → Γ ⊢ e <= τ
  weaken-ana-closed {e} {τ} {Γ} f wt = tr (λ qq → qq ⊢ e <= τ) ∅∪1 (weaken-ana-∪ f wt)

  -- the very structural forms also follow from the union weakening, since
  -- ,, is defined by ∪
  weaken-synth : ∀{ x Γ e τ τ'} → freshe x e
                                  → Γ ⊢ e => τ
                                  → (Γ ,, (x , τ')) ⊢ e => τ
  weaken-synth f wt = weaken-synth-∪ (fresh-freshΓ f) wt

  weaken-ana : ∀{x Γ e τ τ'} → freshe x e
                               → Γ ⊢ e <= τ
                               → (Γ ,, (x , τ')) ⊢ e <= τ
  weaken-ana f wt = weaken-ana-∪ (fresh-freshΓ f) wt


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
    weaken-ta (FFst frsh) (TAFst wt) = TAFst (weaken-ta frsh wt)
    weaken-ta (FSnd frsh) (TASnd wt) = TASnd (weaken-ta frsh wt)
    weaken-ta (FPair frsh frsh₁) (TAPair wt wt₁) = TAPair (weaken-ta frsh wt) (weaken-ta frsh₁ wt₁)
