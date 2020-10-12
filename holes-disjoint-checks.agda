open import Prelude
open import Nat
open import core
open import contexts
open import disjointness


-- this module contains lemmas and properties about the holes-disjoint
-- judgement that double check that it acts as we would expect

module holes-disjoint-checks where
  -- these lemmas are all structurally recursive and quite
  -- mechanical. morally, they establish the properties about reduction
  -- that would be obvious / baked into Agda if holes-disjoint was defined
  -- as a function rather than a judgement (datatype), or if we had defined
  -- all the O(n^2) cases rather than relying on a little indirection to
  -- only have O(n) cases. that work has to go somewhwere, and we prefer
  -- that it goes here.
  ds-lem-asc : ∀{e1 e2 τ} → holes-disjoint e2 e1 → holes-disjoint e2 (e1 ·: τ)
  ds-lem-asc HDConst = HDConst
  ds-lem-asc (HDAsc hd) = HDAsc (ds-lem-asc hd)
  ds-lem-asc HDVar = HDVar
  ds-lem-asc (HDLam1 hd) = HDLam1 (ds-lem-asc hd)
  ds-lem-asc (HDLam2 hd) = HDLam2 (ds-lem-asc hd)
  ds-lem-asc (HDHole x) = HDHole (HNAsc x)
  ds-lem-asc (HDNEHole x hd) = HDNEHole (HNAsc x) (ds-lem-asc hd)
  ds-lem-asc (HDAp hd hd₁) = HDAp (ds-lem-asc hd) (ds-lem-asc hd₁)
  ds-lem-asc (HDFst hd) = HDFst (ds-lem-asc hd)
  ds-lem-asc (HDSnd hd) = HDSnd (ds-lem-asc hd)
  ds-lem-asc (HDPair hd hd₁) = HDPair (ds-lem-asc hd) (ds-lem-asc hd₁)

  ds-lem-lam1 : ∀{e1 e2 x} → holes-disjoint e2 e1 → holes-disjoint e2 (·λ x e1)
  ds-lem-lam1 HDConst = HDConst
  ds-lem-lam1 (HDAsc hd) = HDAsc (ds-lem-lam1 hd)
  ds-lem-lam1 HDVar = HDVar
  ds-lem-lam1 (HDLam1 hd) = HDLam1 (ds-lem-lam1 hd)
  ds-lem-lam1 (HDLam2 hd) = HDLam2 (ds-lem-lam1 hd)
  ds-lem-lam1 (HDHole x₁) = HDHole (HNLam1 x₁)
  ds-lem-lam1 (HDNEHole x₁ hd) = HDNEHole (HNLam1 x₁) (ds-lem-lam1 hd)
  ds-lem-lam1 (HDAp hd hd₁) = HDAp (ds-lem-lam1 hd) (ds-lem-lam1 hd₁)
  ds-lem-lam1 (HDFst hd) = HDFst (ds-lem-lam1 hd)
  ds-lem-lam1 (HDSnd hd) = HDSnd (ds-lem-lam1 hd)
  ds-lem-lam1 (HDPair hd hd₁) = HDPair (ds-lem-lam1 hd) (ds-lem-lam1 hd₁)

  ds-lem-lam2 : ∀{e1 e2 x τ} → holes-disjoint e2 e1 → holes-disjoint e2 (·λ x [ τ ] e1)
  ds-lem-lam2 HDConst = HDConst
  ds-lem-lam2 (HDAsc hd) = HDAsc (ds-lem-lam2 hd)
  ds-lem-lam2 HDVar = HDVar
  ds-lem-lam2 (HDLam1 hd) = HDLam1 (ds-lem-lam2 hd)
  ds-lem-lam2 (HDLam2 hd) = HDLam2 (ds-lem-lam2 hd)
  ds-lem-lam2 (HDHole x₁) = HDHole (HNLam2 x₁)
  ds-lem-lam2 (HDNEHole x₁ hd) = HDNEHole (HNLam2 x₁) (ds-lem-lam2 hd)
  ds-lem-lam2 (HDAp hd hd₁) = HDAp (ds-lem-lam2 hd) (ds-lem-lam2 hd₁)
  ds-lem-lam2 (HDFst hd) = HDFst (ds-lem-lam2 hd)
  ds-lem-lam2 (HDSnd hd) = HDSnd (ds-lem-lam2 hd)
  ds-lem-lam2 (HDPair hd hd₁) = HDPair (ds-lem-lam2 hd) (ds-lem-lam2 hd₁)

  ds-lem-nehole : ∀{e e1 u} → holes-disjoint e e1 → hole-name-new e u → holes-disjoint e ⦇⌜ e1 ⌟⦈[ u ]
  ds-lem-nehole HDConst ν = HDConst
  ds-lem-nehole (HDAsc hd) (HNAsc ν) = HDAsc (ds-lem-nehole hd ν)
  ds-lem-nehole HDVar ν = HDVar
  ds-lem-nehole (HDLam1 hd) (HNLam1 ν) = HDLam1 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDLam2 hd) (HNLam2 ν) = HDLam2 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDHole x) (HNHole x₁) = HDHole (HNNEHole (flip x₁) x)
  ds-lem-nehole (HDNEHole x hd) (HNNEHole x₁ ν) = HDNEHole (HNNEHole (flip x₁) x) (ds-lem-nehole hd ν)
  ds-lem-nehole (HDAp hd hd₁) (HNAp ν ν₁) = HDAp (ds-lem-nehole hd ν) (ds-lem-nehole hd₁ ν₁)
  ds-lem-nehole (HDFst hd) (HNFst v) = HDFst (ds-lem-nehole hd v)
  ds-lem-nehole (HDSnd hd) (HNSnd v) = HDSnd (ds-lem-nehole hd v)
  ds-lem-nehole (HDPair hd hd₁) (HNPair v v₁) = HDPair (ds-lem-nehole hd v) (ds-lem-nehole hd₁ v₁)

  ds-lem-ap : ∀{e1 e2 e3} → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 (e1 ∘ e2)
  ds-lem-ap HDConst hd2 = HDConst
  ds-lem-ap (HDAsc hd1) (HDAsc hd2) = HDAsc (ds-lem-ap hd1 hd2)
  ds-lem-ap HDVar hd2 = HDVar
  ds-lem-ap (HDLam1 hd1) (HDLam1 hd2) = HDLam1 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDLam2 hd1) (HDLam2 hd2) = HDLam2 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDHole x) (HDHole x₁) = HDHole (HNAp x x₁)
  ds-lem-ap (HDNEHole x hd1) (HDNEHole x₁ hd2) = HDNEHole (HNAp x x₁) (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDAp hd1 hd2) (HDAp hd3 hd4) = HDAp (ds-lem-ap hd1 hd3) (ds-lem-ap hd2 hd4)
  ds-lem-ap (HDFst hd) (HDFst hd2) = HDFst (ds-lem-ap hd hd2)
  ds-lem-ap (HDSnd hd) (HDSnd hd2) = HDSnd (ds-lem-ap hd hd2)
  ds-lem-ap (HDPair hd1 hd2) (HDPair hd3 hd4) = HDPair (ds-lem-ap hd1 hd3) (ds-lem-ap hd2 hd4)

  ds-lem-pair : ∀{e1 e2 e3} → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 ⟨ e1 , e2 ⟩
  ds-lem-pair HDConst HDConst = HDConst
  ds-lem-pair (HDAsc hd1) (HDAsc hd2) = HDAsc (ds-lem-pair hd1 hd2)
  ds-lem-pair HDVar HDVar = HDVar
  ds-lem-pair (HDLam1 hd1) (HDLam1 hd2) = HDLam1 (ds-lem-pair hd1 hd2)
  ds-lem-pair (HDLam2 hd1) (HDLam2 hd2) = HDLam2 (ds-lem-pair hd1 hd2)
  ds-lem-pair (HDHole x) (HDHole x₁) = HDHole (HNPair x x₁)
  ds-lem-pair (HDNEHole x hd1) (HDNEHole x₁ hd2) = HDNEHole (HNPair x x₁) (ds-lem-pair hd1 hd2)
  ds-lem-pair (HDAp hd1 hd2) (HDAp hd3 hd4) = HDAp (ds-lem-pair hd1 hd3) (ds-lem-pair hd2 hd4)
  ds-lem-pair (HDFst hd1) (HDFst hd2) = HDFst (ds-lem-pair hd1 hd2)
  ds-lem-pair (HDSnd hd1) (HDSnd hd2) = HDSnd (ds-lem-pair hd1 hd2)
  ds-lem-pair (HDPair hd1 hd2) (HDPair hd3 hd4) = HDPair (ds-lem-pair hd1 hd3) (ds-lem-pair hd2 hd4)

  ds-lem-fst : ∀{e e'} → holes-disjoint e' e → holes-disjoint e' (fst e)
  ds-lem-fst HDConst = HDConst
  ds-lem-fst (HDAsc hd) = HDAsc (ds-lem-fst hd)
  ds-lem-fst HDVar = HDVar
  ds-lem-fst (HDLam1 hd) = HDLam1 (ds-lem-fst hd)
  ds-lem-fst (HDLam2 hd) = HDLam2 (ds-lem-fst hd)
  ds-lem-fst (HDHole x) = HDHole (HNFst x)
  ds-lem-fst (HDNEHole x hd) = HDNEHole (HNFst x) (ds-lem-fst hd)
  ds-lem-fst (HDAp hd hd₁) = HDAp (ds-lem-fst hd) (ds-lem-fst hd₁)
  ds-lem-fst (HDFst hd) = HDFst (ds-lem-fst hd)
  ds-lem-fst (HDSnd hd) = HDSnd (ds-lem-fst hd)
  ds-lem-fst (HDPair hd hd₁) = HDPair (ds-lem-fst hd) (ds-lem-fst hd₁)

  ds-lem-snd : ∀{e e'} → holes-disjoint e' e → holes-disjoint e' (snd e)
  ds-lem-snd HDConst = HDConst
  ds-lem-snd (HDAsc hd) = HDAsc (ds-lem-snd hd)
  ds-lem-snd HDVar = HDVar
  ds-lem-snd (HDLam1 hd) = HDLam1 (ds-lem-snd hd)
  ds-lem-snd (HDLam2 hd) = HDLam2 (ds-lem-snd hd)
  ds-lem-snd (HDHole x) = HDHole (HNSnd x)
  ds-lem-snd (HDNEHole x hd) = HDNEHole (HNSnd x) (ds-lem-snd hd)
  ds-lem-snd (HDAp hd hd₁) = HDAp (ds-lem-snd hd) (ds-lem-snd hd₁)
  ds-lem-snd (HDFst hd) = HDFst (ds-lem-snd hd)
  ds-lem-snd (HDSnd hd) = HDSnd (ds-lem-snd hd)
  ds-lem-snd (HDPair hd hd₁) = HDPair (ds-lem-snd hd) (ds-lem-snd hd₁)

  -- holes-disjoint is symmetric
  disjoint-sym : (e1 e2 : eexp) → holes-disjoint e1 e2 → holes-disjoint e2 e1
  disjoint-sym .c c HDConst = HDConst
  disjoint-sym .c (e2 ·: x) HDConst = HDAsc (disjoint-sym _ _ HDConst)
  disjoint-sym .c (X x) HDConst = HDVar
  disjoint-sym .c (·λ x e2) HDConst = HDLam1 (disjoint-sym c e2 HDConst)
  disjoint-sym .c (·λ x [ x₁ ] e2) HDConst = HDLam2 (disjoint-sym c e2 HDConst)
  disjoint-sym .c ⦇⦈[ x ] HDConst = HDHole HNConst
  disjoint-sym .c ⦇⌜ e2 ⌟⦈[ x ] HDConst = HDNEHole HNConst (disjoint-sym c e2 HDConst)
  disjoint-sym .c (e2 ∘ e3) HDConst = HDAp (disjoint-sym c e2 HDConst) (disjoint-sym c e3 HDConst)
  disjoint-sym .c ⟨ e2 , e3 ⟩ HDConst = HDPair (disjoint-sym c e2 HDConst) (disjoint-sym c e3 HDConst)
  disjoint-sym .c (fst e2) HDConst = HDFst (disjoint-sym c e2 HDConst)
  disjoint-sym .c (snd e2) HDConst = HDSnd (disjoint-sym c e2 HDConst)

  disjoint-sym _ c (HDAsc hd) = HDConst
  disjoint-sym _ (e2 ·: x) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x) (HDAsc hd) | HDAsc ih = HDAsc (ds-lem-asc ih)
  disjoint-sym _ (X x) (HDAsc hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDAsc hd) | HDLam1 ih = HDLam1 (ds-lem-asc ih)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDAsc hd) | HDLam2 ih = HDLam2 (ds-lem-asc ih)
  disjoint-sym _ ⦇⦈[ x ] (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x ] (HDAsc hd) | HDHole x₁ = HDHole (HNAsc x₁)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDAsc hd) | HDNEHole x₁ ih = HDNEHole (HNAsc x₁) (ds-lem-asc ih)
  disjoint-sym _ (e2 ∘ e3) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDAsc hd) | HDAp ih ih₁ = HDAp (ds-lem-asc ih) (ds-lem-asc ih₁)
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym .(_ ·: _) ⟨ e2 , e3 ⟩ (HDAsc hd) | HDPair ih ih₁ = HDPair (ds-lem-asc ih) (ds-lem-asc ih₁)
  disjoint-sym _ (fst e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym .(_ ·: _) (fst e2) (HDAsc hd) | HDFst ih = HDFst (ds-lem-asc ih)
  disjoint-sym _ (snd e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym .(_ ·: _) (snd e2) (HDAsc hd) | HDSnd ih = HDSnd (ds-lem-asc ih)

  disjoint-sym _ c HDVar = HDConst
  disjoint-sym _ (e2 ·: x₁) HDVar = HDAsc (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (X x₁) HDVar = HDVar
  disjoint-sym _ (·λ x₁ e2) HDVar = HDLam1 (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) HDVar = HDLam2 (disjoint-sym _ e2 HDVar)
  disjoint-sym _ ⦇⦈[ x₁ ] HDVar = HDHole HNVar
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] HDVar = HDNEHole HNVar (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (e2 ∘ e3) HDVar = HDAp (disjoint-sym _ e2 HDVar) (disjoint-sym _ e3 HDVar)
  disjoint-sym _ ⟨ e2 , e3 ⟩ HDVar = HDPair (disjoint-sym (X _) e2 HDVar)
                                       (disjoint-sym (X _) e3 HDVar)
  disjoint-sym _ (fst e2) HDVar = HDFst (disjoint-sym (X _) e2 HDVar)
  disjoint-sym _ (snd e2) HDVar = HDSnd (disjoint-sym (X _) e2 HDVar)

  disjoint-sym _ c (HDLam1 hd) = HDConst
  disjoint-sym _ (e2 ·: x₁) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x₁) (HDLam1 hd) | HDAsc ih = HDAsc (ds-lem-lam1 ih)
  disjoint-sym _ (X x₁) (HDLam1 hd) = HDVar
  disjoint-sym _ (·λ x₁ e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ e2) (HDLam1 hd) | HDLam1 ih = HDLam1 (ds-lem-lam1 ih)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam1 hd) | HDLam2 ih = HDLam2 (ds-lem-lam1 ih)
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam1 hd) | HDHole x = HDHole (HNLam1 x)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] (HDLam1 hd) | HDNEHole x ih = HDNEHole (HNLam1 x) (ds-lem-lam1 ih)
  disjoint-sym _ (e2 ∘ e3) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDLam1 hd) | HDAp ih ih₁ = HDAp (ds-lem-lam1 ih) (ds-lem-lam1 ih₁)
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDLam1 hd) | HDPair ih ih₁ = HDPair (ds-lem-lam1 ih) (ds-lem-lam1 ih₁)
  disjoint-sym _ (fst e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (fst e2) (HDLam1 hd) | HDFst ih = HDFst (ds-lem-lam1 ih)
  disjoint-sym _ (snd e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (snd e2) (HDLam1 hd) | HDSnd ih = HDSnd (ds-lem-lam1 ih)

  disjoint-sym _ c (HDLam2 hd) = HDConst
  disjoint-sym _ (e2 ·: x₁) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x₁) (HDLam2 hd) | HDAsc ih = HDAsc (ds-lem-lam2 ih)
  disjoint-sym _ (X x₁) (HDLam2 hd) = HDVar
  disjoint-sym _ (·λ x₁ e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ e2) (HDLam2 hd) | HDLam1 ih = HDLam1 (ds-lem-lam2 ih)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam2 hd) | HDLam2 ih = HDLam2 (ds-lem-lam2 ih)
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x₁ ] (HDLam2 hd) | HDHole x = HDHole (HNLam2 x)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] (HDLam2 hd) | HDNEHole x ih = HDNEHole (HNLam2 x) (ds-lem-lam2 ih)
  disjoint-sym _ (e2 ∘ e3) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDLam2 hd) | HDAp ih ih₁ = HDAp (ds-lem-lam2 ih) (ds-lem-lam2 ih₁)
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDLam2 hd) | HDPair ih ih₁ = HDPair (ds-lem-lam2 ih) (ds-lem-lam2 ih₁)
  disjoint-sym _ (fst e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (fst e2) (HDLam2 hd) | HDFst ih = HDFst (ds-lem-lam2 ih)
  disjoint-sym _ (snd e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (snd e2) (HDLam2 hd) | HDSnd ih = HDSnd (ds-lem-lam2 ih)

  disjoint-sym _ c (HDHole x) = HDConst
  disjoint-sym _ (e2 ·: x) (HDHole (HNAsc x₁)) = HDAsc (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (X x) (HDHole x₁) = HDVar
  disjoint-sym _ (·λ x e2) (HDHole (HNLam1 x₁)) = HDLam1 (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDHole (HNLam2 x₂)) = HDLam2 (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₂))
  disjoint-sym _ ⦇⦈[ x ] (HDHole (HNHole x₁)) =  HDHole (HNHole (flip x₁))
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ u' ] (HDHole (HNNEHole x x₁)) = HDNEHole (HNHole (flip x)) (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (e2 ∘ e3) (HDHole (HNAp x x₁)) = HDAp (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x))
                                                    (disjoint-sym ⦇⦈[ _ ] e3 (HDHole x₁))
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDHole (HNPair x1 x2)) = HDPair (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x1)) (disjoint-sym ⦇⦈[ _ ] e3 (HDHole x2))
  disjoint-sym _ (fst e2) (HDHole (HNFst x)) = HDFst (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x))
  disjoint-sym _ (snd e2) (HDHole (HNSnd x)) = HDSnd (disjoint-sym ⦇⦈[ _ ] e2 (HDHole x))

  disjoint-sym _ c (HDNEHole x hd) = HDConst
  disjoint-sym _ (e2 ·: x) (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e ·: x) (HDNEHole (HNAsc x₁) hd) | HDAsc ih = HDAsc (ds-lem-nehole ih x₁)
  disjoint-sym _ (X x) (HDNEHole x₁ hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDNEHole (HNLam1 x₁) hd) | HDLam1 ih = HDLam1 (ds-lem-nehole ih x₁)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDNEHole x₂ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDNEHole (HNLam2 x₂) hd) | HDLam2 ih = HDLam2 (ds-lem-nehole ih x₂)
  disjoint-sym _ ⦇⦈[ x ] (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x ] (HDNEHole (HNHole x₂) hd) | HDHole x₁ = HDHole (HNNEHole (flip x₂) x₁)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDNEHole (HNNEHole x₂ x₃) hd) | HDNEHole x₁ ih = HDNEHole (HNNEHole (flip x₂) x₁) (ds-lem-nehole ih x₃)
  disjoint-sym _ (e2 ∘ e3) (HDNEHole x hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e1 ∘ e3) (HDNEHole (HNAp x x₁) hd) | HDAp ih ih₁ = HDAp (ds-lem-nehole ih x) (ds-lem-nehole ih₁ x₁)
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDNEHole x hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDNEHole (HNPair x x₁) hd) | HDPair ih ih₁ = HDPair (ds-lem-nehole ih x) (ds-lem-nehole ih₁ x₁)
  disjoint-sym _ (fst e2) (HDNEHole x hd) with disjoint-sym _ _ hd
  disjoint-sym _ (fst e2) (HDNEHole (HNFst x1) hd) | HDFst ih = HDFst (ds-lem-nehole ih x1)
  disjoint-sym _ (snd e2) (HDNEHole x hd) with disjoint-sym _ _ hd
  disjoint-sym _ (snd e2) (HDNEHole (HNSnd x1) hd) | HDSnd ih = HDSnd (ds-lem-nehole ih x1)

  disjoint-sym _ c (HDAp hd hd₁) = HDConst
  disjoint-sym _ (e3 ·: x) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ·: x) (HDAp hd hd₁) | HDAsc ih | HDAsc ih1 = HDAsc (ds-lem-ap ih ih1)
  disjoint-sym _ (X x) (HDAp hd hd₁) = HDVar
  disjoint-sym _ (·λ x e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x e3) (HDAp hd hd₁) | HDLam1 ih | HDLam1 ih1 = HDLam1 (ds-lem-ap ih ih1)
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDAp hd hd₁) | HDLam2 ih | HDLam2 ih1 = HDLam2 (ds-lem-ap ih ih1)
  disjoint-sym _ ⦇⦈[ x ] (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇⦈[ x ] (HDAp hd hd₁) | HDHole x₁ | HDHole x₂ = HDHole (HNAp x₁ x₂)
  disjoint-sym _ ⦇⌜ e3 ⌟⦈[ x ] (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇⌜ e3 ⌟⦈[ x ] (HDAp hd hd₁) | HDNEHole x₁ ih | HDNEHole x₂ ih1 = HDNEHole (HNAp x₁ x₂) (ds-lem-ap ih ih1)
  disjoint-sym _ (e3 ∘ e4) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ∘ e4) (HDAp hd hd₁) | HDAp ih ih₁ | HDAp ih1 ih2 = HDAp (ds-lem-ap ih ih1) (ds-lem-ap ih₁ ih2)
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDAp hd hd₁) | HDPair ih ih₁ | HDPair ih1 ih2 = HDPair (ds-lem-ap ih ih1) (ds-lem-ap ih₁ ih2)
  disjoint-sym _ (fst e2) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (fst e2) (HDAp hd hd₁) | HDFst ih | HDFst ih1 = HDFst (ds-lem-ap ih ih1)
  disjoint-sym _ (snd e2) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (snd e2) (HDAp hd hd₁) | HDSnd ih | HDSnd ih1 = HDSnd (ds-lem-ap ih ih1)

  disjoint-sym _ c (HDFst hd) = HDConst
  disjoint-sym _ (e2 ·: x) (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x) (HDFst hd) | HDAsc ih = HDAsc (ds-lem-fst ih)
  disjoint-sym _ (X x) (HDFst hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDFst hd) | HDLam1 ih = HDLam1 (ds-lem-fst ih)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDFst hd) | HDLam2 ih = HDLam2 (ds-lem-fst ih)
  disjoint-sym _ ⦇⦈[ x ] (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x ] (HDFst hd) | HDHole ih = HDHole (HNFst ih)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDFst hd) | HDNEHole x₁ ih = HDNEHole (HNFst x₁) (ds-lem-fst ih)
  disjoint-sym _ (e2 ∘ e3) (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDFst hd) | HDAp ih ih₁ = HDAp (ds-lem-fst ih) (ds-lem-fst ih₁)
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDFst hd) | HDPair ih ih₁ = HDPair (ds-lem-fst ih) (ds-lem-fst ih₁)
  disjoint-sym _ (fst e2) (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ (fst e2) (HDFst hd) | HDFst ih = HDFst (ds-lem-fst ih)
  disjoint-sym _ (snd e2) (HDFst hd) with disjoint-sym _ _ hd
  disjoint-sym _ (snd e2) (HDFst hd) | HDSnd ih = HDSnd (ds-lem-fst ih)

  disjoint-sym _ c (HDSnd hd) = HDConst
  disjoint-sym _ (e2 ·: x) (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x) (HDSnd hd) | HDAsc ih = HDAsc (ds-lem-snd ih)
  disjoint-sym _ (X x) (HDSnd hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDSnd hd) | HDLam1 ih = HDLam1 (ds-lem-snd ih)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDSnd hd) | HDLam2 ih = HDLam2 (ds-lem-snd ih)
  disjoint-sym _ ⦇⦈[ x ] (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⦈[ x ] (HDSnd hd) | HDHole ih = HDHole (HNSnd ih)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDSnd hd) | HDNEHole x₁ ih = HDNEHole (HNSnd x₁) (ds-lem-snd ih)
  disjoint-sym _ (e2 ∘ e3) (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDSnd hd) | HDAp ih ih₁ = HDAp (ds-lem-snd ih) (ds-lem-snd ih₁)
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDSnd hd) | HDPair ih ih₁ = HDPair (ds-lem-snd ih) (ds-lem-snd ih₁)
  disjoint-sym _ (fst e2) (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ (fst e2) (HDSnd hd) | HDFst ih = HDFst (ds-lem-snd ih)
  disjoint-sym _ (snd e2) (HDSnd hd) with disjoint-sym _ _ hd
  disjoint-sym _ (snd e2) (HDSnd hd) | HDSnd ih = HDSnd (ds-lem-snd ih)

  disjoint-sym _ c (HDPair hd hd₁) = HDConst
  disjoint-sym _ (e3 ·: x) (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ·: x) (HDPair hd hd₁) | HDAsc ih | HDAsc ih1 = HDAsc (ds-lem-pair ih ih1)
  disjoint-sym _ (X x) (HDPair hd hd₁) = HDVar
  disjoint-sym _ (·λ x e3) (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x e3) (HDPair hd hd₁) | HDLam1 ih | HDLam1 ih1 = HDLam1 (ds-lem-pair ih ih1)
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDPair hd hd₁) | HDLam2 ih | HDLam2 ih1 = HDLam2 (ds-lem-pair ih ih1)
  disjoint-sym _ ⦇⦈[ x ] (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇⦈[ x ] (HDPair hd hd₁) | HDHole x₁ | HDHole x₂ = HDHole (HNPair x₁ x₂)
  disjoint-sym _ ⦇⌜ e3 ⌟⦈[ x ] (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇⌜ e3 ⌟⦈[ x ] (HDPair hd hd₁) | HDNEHole x₁ ih | HDNEHole x₂ ih1 = HDNEHole (HNPair x₁ x₂) (ds-lem-pair ih ih1)
  disjoint-sym _ (e3 ∘ e4) (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ∘ e4) (HDPair hd hd₁) | HDAp ih ih₁ | HDAp ih1 ih2 = HDAp (ds-lem-pair ih ih1) (ds-lem-pair ih₁ ih2)
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⟨ e2 , e3 ⟩ (HDPair hd hd₁) | HDPair ih ih₁ | HDPair ih1 ih2 = HDPair (ds-lem-pair ih ih1) (ds-lem-pair ih₁ ih2)
  disjoint-sym _ (fst e2) (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (fst e2) (HDPair hd hd₁) | HDFst ih | HDFst ih1 = HDFst (ds-lem-pair ih ih1)
  disjoint-sym _ (snd e2) (HDPair hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (snd e2) (HDPair hd hd₁) | HDSnd ih | HDSnd ih1 = HDSnd (ds-lem-pair ih ih1)

  -- note that this is false, so holes-disjoint isn't transitive
  -- disjoint-new : ∀{e1 e2 u} → holes-disjoint e1 e2 → hole-name-new e1 u → hole-name-new e2 u

  -- it's also not reflexive, because ⦇⦈[ u ] isn't hole-disjoint with
  -- itself since refl : u == u; it's also not anti-reflexive, because the
  -- expression c *is* hole-disjoint with itself (albeit vacuously)
