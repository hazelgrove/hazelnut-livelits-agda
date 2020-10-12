open import Prelude
open import core
open import contexts

module synth-unicity where
  -- synthesis only produces equal types. note that there is no need for an
  -- analagous theorem for analytic positions because we think of
  -- the type as an input
  synthunicity : {Γ : tctx} {e : eexp} {t t' : typ} →
                  (Γ ⊢ e => t)
                → (Γ ⊢ e => t')
                → t == t'
  synthunicity (SAsc _) (SAsc _) = refl
  synthunicity {Γ = G} (SVar in1) (SVar in2) = ctxunicity {Γ = G} in1 in2
  synthunicity (SAp _  D1 MAHole _) (SAp _ D2 MAHole y) = refl
  synthunicity (SAp _ D1 MAHole _) (SAp _ D2 MAArr y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp _ D1 MAArr _) (SAp _ D2 MAHole y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp _ D1 MAArr _) (SAp _ D2 MAArr y) with synthunicity D1 D2
  ... | refl = refl
  synthunicity SEHole SEHole = refl
  synthunicity (SNEHole _ _) (SNEHole _ _) = refl
  synthunicity SConst SConst = refl
  synthunicity (SLam _ D1) (SLam _ D2) with synthunicity D1 D2
  synthunicity (SLam x₁ D1) (SLam x₂ D2) | refl = refl
  synthunicity (SFst D1 h1) (SFst D2 h2) with synthunicity D1 D2
  synthunicity (SFst D1 MPHole) (SFst D2 MPHole) | refl = refl
  synthunicity (SFst D1 MPProd) (SFst D2 MPProd) | refl = refl
  synthunicity (SSnd D1 h1) (SSnd D2 h2) with synthunicity D1 D2
  synthunicity (SSnd D1 MPHole) (SSnd D2 MPHole) | refl = refl
  synthunicity (SSnd D1 MPProd) (SSnd D2 MPProd) | refl = refl
  synthunicity (SPair hd1 x x₁) (SPair hd2 x₂ x₃) with synthunicity x x₂ | synthunicity x₁ x₃
  synthunicity (SPair hd1 x x₁) (SPair hd2 x₂ x₃) | refl | refl = refl
