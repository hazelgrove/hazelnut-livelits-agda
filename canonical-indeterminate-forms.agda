open import Nat
open import Prelude
open import contexts
open import core
open import type-assignment-unicity

module canonical-indeterminate-forms where

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at base type
  data cif-base : (Δ : hctx) (d : ihexp) → Set where
    CIFBEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⦈⟨ u , σ ⟩) ×
         ((u :: b [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
       → cif-base Δ d
    CIFBNEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: b [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
        → cif-base Δ d
    CIFBAp : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: τ2 ==> b) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-base Δ d
    CIFBFst : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ2 ∈ htyp ]
        ((d == fst d') ×
         (Δ , ∅ ⊢ d' :: b ⊗ τ2) ×
         (d' indet) ×
         (∀{d1 d2} → d' ≠ ⟨ d1 , d2 ⟩)
        )
        → cif-base Δ d
    CIFBSnd : ∀{Δ d} →
        Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ]
        ((d == snd d') ×
         (Δ , ∅ ⊢ d' :: τ1 ⊗ b) ×
         (d' indet) ×
         (∀{d1 d2} → d' ≠ ⟨ d1 , d2 ⟩)
        )
        → cif-base Δ d
    CIFBCast : ∀ {Δ d} →
      Σ[ d' ∈ ihexp ]
        ((d == d' ⟨ ⦇⦈ ⇒ b ⟩) ×
         (Δ , ∅ ⊢ d' :: ⦇⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇⦈ ⟩))
        )
        → cif-base Δ d
    CIFBFailedCast : ∀ {Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == d' ⟨ τ' ⇒⦇⦈⇏ b ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (τ' ≠ b)
        )
       → cif-base Δ d

  canonical-indeterminate-forms-base : ∀{Δ d} →
                                       Δ , ∅ ⊢ d :: b →
                                       d indet →
                                       cif-base Δ d
  canonical-indeterminate-forms-base TAConst ()
  canonical-indeterminate-forms-base (TAVar x₁) ()
  canonical-indeterminate-forms-base (TAAp wt wt₁) (IAp x ind x₁) = CIFBAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-base (TAEHole x x₁) IEHole = CIFBEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-base (TANEHole x wt x₁) (INEHole x₂) = CIFBNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-base (TACast wt x) (ICastHoleGround x₁ ind x₂) = CIFBCast (_ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-base (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) = CIFBFailedCast (_ , _ , refl , x , x₅ , x₇)
  canonical-indeterminate-forms-base (TAFst wt) (IFst ind x _) = CIFBFst (_ , _ , refl , wt , ind , x)
  canonical-indeterminate-forms-base (TASnd wt) (ISnd ind x _) = CIFBSnd (_ , _ , refl , wt , ind , x)

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at arrow type
  data cif-arr : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CIFAEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⦈⟨ u , σ ⟩) ×
         ((u :: (τ1 ==> τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-arr Δ d τ1 τ2
    CIFANEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: (τ1 ==> τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
        → cif-arr Δ d τ1 τ2
    CIFAAp : ∀{d Δ τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2' ∈ htyp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: τ2' ==> (τ1 ==> τ2)) ×
         (Δ , ∅ ⊢ d2 :: τ2') ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFAFst : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == fst d') ×
         (Δ , ∅ ⊢ d' :: (τ1 ==> τ2) ⊗ τ') ×
         (d' indet) ×
         (∀{d1 d2} → d' ≠ ⟨ d1 , d2 ⟩)
        )
        → cif-arr Δ d τ1 τ2
    CIFASnd : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == snd d') ×
         (Δ , ∅ ⊢ d' :: τ' ⊗ (τ1 ==> τ2)) ×
         (d' indet) ×
         (∀{d1 d2} → d' ≠ ⟨ d1 , d2 ⟩)
        )
        → cif-arr Δ d τ1 τ2
    CIFACast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == d' ⟨ (τ1' ==> τ2') ⇒ (τ1 ==> τ2) ⟩) ×
          (Δ , ∅ ⊢ d' :: τ1' ==> τ2') ×
          (d' indet) ×
          ((τ1' ==> τ2') ≠ (τ1 ==> τ2))
        )
       → cif-arr Δ d τ1 τ2
    CIFACastHole : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == (d' ⟨ ⦇⦈ ⇒ ⦇⦈ ==> ⦇⦈ ⟩)) ×
         (τ1 == ⦇⦈) ×
         (τ2 == ⦇⦈) ×
         (Δ , ∅ ⊢ d' :: ⦇⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇⦈ ⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFAFailedCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
          ((d == (d' ⟨ τ' ⇒⦇⦈⇏ ⦇⦈ ==> ⦇⦈ ⟩) ) ×
           (τ1 == ⦇⦈) ×
           (τ2 == ⦇⦈) ×
           (Δ , ∅ ⊢ d' :: τ') ×
           (τ' ground) ×
           (τ' ≠ (⦇⦈ ==> ⦇⦈))
           )
          → cif-arr Δ d τ1 τ2

  canonical-indeterminate-forms-arr : ∀{Δ d τ1 τ2 } →
                                       Δ , ∅ ⊢ d :: (τ1 ==> τ2) →
                                       d indet →
                                       cif-arr Δ d τ1 τ2
  canonical-indeterminate-forms-arr (TAVar x₁) ()
  canonical-indeterminate-forms-arr (TALam _ wt) ()
  canonical-indeterminate-forms-arr (TAAp wt wt₁) (IAp x ind x₁) = CIFAAp (_ , _ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-arr (TAEHole x x₁) IEHole = CIFAEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-arr (TANEHole x wt x₁) (INEHole x₂) = CIFANEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-arr (TACast wt x) (ICastArr x₁ ind) = CIFACast (_ , _ , _ , _ , _ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-arr (TACast wt TCHole2) (ICastHoleGround x₁ ind GHole) = CIFACastHole (_ , refl , refl , refl , wt , ind , x₁)
  canonical-indeterminate-forms-arr (TAFailedCast x x₁ GHole x₃) (IFailedCast x₄ x₅ GHole x₇) = CIFAFailedCast (_ , _ , refl , refl , refl , x , x₅ , x₇)
  canonical-indeterminate-forms-arr (TAFst wt) (IFst ind x _) = CIFAFst (_ , _ , refl , wt , ind , x)
  canonical-indeterminate-forms-arr (TASnd wt) (ISnd ind x _) = CIFASnd (_ , _ , refl , wt , ind , x)

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at hole type
  data cif-hole : (Δ : hctx) (d : ihexp) → Set where
    CIFHEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⦈⟨ u , σ ⟩) ×
         ((u :: ⦇⦈ [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-hole Δ d
    CIFHNEHole : ∀ {Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: ⦇⦈ [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-hole Δ d
    CIFHAp : ∀ {Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: (τ2 ==> ⦇⦈)) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
      → cif-hole Δ d
    CIFHFst : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
       ((d == fst d') ×
        (Δ , ∅ ⊢ d' :: ⦇⦈ ⊗ τ') ×
        (d' indet) ×
        (∀{d1 d2} → d' ≠ ⟨ d1 , d2 ⟩)
       )
      → cif-hole Δ d
    CIFHSnd : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
       ((d == snd d') ×
        (Δ , ∅ ⊢ d' :: τ' ⊗ ⦇⦈) ×
        (d' indet) ×
        (∀{d1 d2} → d' ≠ ⟨ d1 , d2 ⟩)
       )
      → cif-hole Δ d
    CIFHCast : ∀ {Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == d' ⟨ τ' ⇒ ⦇⦈ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (d' indet)
        )
      → cif-hole Δ d

  canonical-indeterminate-forms-hole : ∀{Δ d} →
                                       Δ , ∅ ⊢ d :: ⦇⦈ →
                                       d indet →
                                       cif-hole Δ d
  canonical-indeterminate-forms-hole (TAVar x₁) ()
  canonical-indeterminate-forms-hole (TAAp wt wt₁) (IAp x ind x₁) = CIFHAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-hole (TAEHole x x₁) IEHole = CIFHEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-hole (TANEHole x wt x₁) (INEHole x₂) = CIFHNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-hole (TACast wt x) (ICastGroundHole x₁ ind) = CIFHCast (_ , _ , refl , wt , x₁ , ind)
  canonical-indeterminate-forms-hole (TACast wt x) (ICastHoleGround x₁ ind ())
  canonical-indeterminate-forms-hole (TAFailedCast x x₁ () x₃) (IFailedCast x₄ x₅ x₆ x₇)
  canonical-indeterminate-forms-hole (TAFst wt) (IFst ind x _) = CIFHFst (_ , _ , refl , wt , ind , x)
  canonical-indeterminate-forms-hole (TASnd wt) (ISnd ind x _) = CIFHSnd (_ , _ , refl , wt , ind , x)

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at product type
  data cif-prod : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CIFPEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⦈⟨ u , σ ⟩) ×
         ((u :: (τ1 ⊗ τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-prod Δ d τ1 τ2
    CIFPNEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: (τ1 ⊗ τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
        → cif-prod Δ d τ1 τ2
    CIFPAp : ∀{d Δ τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2' ∈ htyp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: τ2' ==> (τ1 ⊗ τ2)) ×
         (Δ , ∅ ⊢ d2 :: τ2') ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-prod Δ d τ1 τ2
    CIFPFst : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == fst d') ×
         (Δ , ∅ ⊢ d' :: (τ1 ⊗ τ2) ⊗ τ') ×
         (d' indet) ×
         (∀{d1 d2} → d' ≠ ⟨ d1 , d2 ⟩)
        )
        → cif-prod Δ d τ1 τ2
    CIFPSnd : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == snd d') ×
         (Δ , ∅ ⊢ d' :: τ' ⊗ (τ1 ⊗ τ2)) ×
         (d' indet) ×
         (∀{d1 d2} → d' ≠ ⟨ d1 , d2 ⟩)
        )
        → cif-prod Δ d τ1 τ2
    CIFPPair1 : ∀{Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ]
        ((d == ⟨ d1 , d2 ⟩) ×
         (Δ , ∅ ⊢ d1 :: τ1) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         d1 indet ×
         d2 final
        )
        → cif-prod Δ d τ1 τ2
    CIFPPair2 : ∀{Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ]
        ((d == ⟨ d1 , d2 ⟩) ×
         (Δ , ∅ ⊢ d1 :: τ1) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         d1 final ×
         d2 indet
        )
        → cif-prod Δ d τ1 τ2
    CIFPCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == d' ⟨ (τ1' ⊗ τ2') ⇒ (τ1 ⊗ τ2) ⟩) ×
          (Δ , ∅ ⊢ d' :: τ1' ⊗ τ2') ×
          (d' indet) ×
          ((τ1' ⊗ τ2') ≠ (τ1 ⊗ τ2))
        )
       → cif-prod Δ d τ1 τ2
    CIFPCastHole : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == (d' ⟨ ⦇⦈ ⇒ ⦇⦈ ⊗ ⦇⦈ ⟩)) ×
         (τ1 == ⦇⦈) ×
         (τ2 == ⦇⦈) ×
         (Δ , ∅ ⊢ d' :: ⦇⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇⦈ ⟩))
        )
        → cif-prod Δ d τ1 τ2
    CIFPFailedCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
          ((d == (d' ⟨ τ' ⇒⦇⦈⇏ ⦇⦈ ⊗ ⦇⦈ ⟩) ) ×
           (τ1 == ⦇⦈) ×
           (τ2 == ⦇⦈) ×
           (Δ , ∅ ⊢ d' :: τ') ×
           (τ' ground) ×
           (τ' ≠ (⦇⦈ ⊗ ⦇⦈))
           )
          → cif-prod Δ d τ1 τ2

  canonical-indeterminate-forms-prod : ∀{Δ d τ1 τ2 } →
                                       Δ , ∅ ⊢ d :: (τ1 ⊗ τ2) →
                                       d indet →
                                       cif-prod Δ d τ1 τ2
  canonical-indeterminate-forms-prod (TAVar x₁) ()
  canonical-indeterminate-forms-prod (TAAp wt wt₁) (IAp x ind x₁) = CIFPAp (_ , _ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-prod (TAEHole x x₁) IEHole = CIFPEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-prod (TANEHole x wt x₁) (INEHole x₂) = CIFPNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-prod (TACast wt x) (ICastProd x₁ ind) = CIFPCast (_ , _ , _ , _ , _ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-prod (TACast wt TCHole2) (ICastHoleGround x₁ ind GProd) = CIFPCastHole (_ , refl , refl , refl , wt , ind , x₁)
  canonical-indeterminate-forms-prod (TAFailedCast wt x GProd x₂) (IFailedCast x₃ x₄ x₅ x₆) = CIFPFailedCast (_ , _ , refl , refl , refl , wt , x₄ , x₆)
  canonical-indeterminate-forms-prod (TAFst wt) (IFst ind x _) = CIFPFst (_ , _ , refl , wt , ind , x)
  canonical-indeterminate-forms-prod (TASnd wt) (ISnd ind x _) = CIFPSnd (_ , _ , refl , wt , ind , x)
  canonical-indeterminate-forms-prod (TAPair wt wt₁) (IPair1 ind x) = CIFPPair1 (_ , _ , refl , wt , wt₁ , ind , x)
  canonical-indeterminate-forms-prod (TAPair wt wt₁) (IPair2 x ind) = CIFPPair2 (_ , _ , refl , wt , wt₁ , x , ind)

  canonical-indeterminate-forms-coverage : ∀{Δ d τ} →
                                           Δ , ∅ ⊢ d :: τ →
                                           d indet →
                                           τ ≠ b →
                                           ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                           τ ≠ ⦇⦈ →
                                           ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ⊗ τ2)) →
                                           ⊥
  canonical-indeterminate-forms-coverage TAConst () nb na nh
  canonical-indeterminate-forms-coverage (TAVar x₁) () nb na nh
  canonical-indeterminate-forms-coverage (TALam _ wt) () nb na nh
  canonical-indeterminate-forms-coverage {τ = b} (TAAp wt wt₁) (IAp x ind x₁) nb na nh _ = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TAAp wt wt₁) (IAp x ind x₁) nb na nh _ = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAAp wt wt₁) (IAp x ind x₁) nb na nh _ = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = b} (TAEHole x x₁) IEHole nb na nh _ = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TAEHole x x₁) IEHole nb na nh _ = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAEHole x x₁) IEHole nb na nh _ = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = b} (TANEHole x wt x₁) (INEHole x₂) nb na nh _ = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TANEHole x wt x₁) (INEHole x₂) nb na nh _ = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TANEHole x wt x₁) (INEHole x₂) nb na nh _ = na τ τ₁ refl
  canonical-indeterminate-forms-coverage (TACast wt x) (ICastArr x₁ ind) nb na nh _ = na _ _ refl
  canonical-indeterminate-forms-coverage (TACast wt x) (ICastGroundHole x₁ ind) nb na nh _ = nh refl
  canonical-indeterminate-forms-coverage {τ = b} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh _ = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh _ = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh _ = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = b} (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) z _ _ _ = z refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) _ _ z _ = z refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) _ z _ _ = z τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = b} (TAFst wt) (IFst ind x _) nb na nh np = nb refl
  canonical-indeterminate-forms-coverage {τ = b} (TASnd wt) (ISnd ind x _) nb na nh np = nb refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TAFst wt) (IFst ind x _) nb na nh np = nh refl
  canonical-indeterminate-forms-coverage {τ = ⦇⦈} (TASnd wt) (ISnd ind x _) nb na nh np = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TAFst wt) (IFst ind x _) nb na nh np = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} (TASnd wt) (ISnd ind x _) nb na nh np = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TAAp wt wt₁) (IAp x ind x₁) nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TAEHole x x₁) IEHole nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TANEHole x wt x₁) (INEHole x₂) nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TACast wt x) (ICastProd x₁ ind) nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TACast wt x) (ICastHoleGround x₁ ind x₂) nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TAFailedCast wt x x₁ x₂) (IFailedCast x₃ x₄ x₅ x₆) nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TAFst wt) (IFst ind x _) nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TASnd wt) (ISnd ind x _) nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TAPair wt wt₁) (IPair1 ind x) nb na nh np = np τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊗ τ₁} (TAPair wt wt₁) (IPair2 x ind) nb na nh np = np τ τ₁ refl
