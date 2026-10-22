/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ReconstructionMappedExt
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateUniqueness
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCandidateMonicity

/-! # Original ambient embeddings of genuine global bounded candidates -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u v
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H G : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (a : G ⟶ H) (β : (completionFunctor X K).obj G ≅ F)
  (hβ : β.hom ≫ α = (completionFunctor X K).map a)

/-- The specified candidate's original stage maps. -/
def boundedCandidateStages : (Functor.const ℕᵒᵖ).obj G.obj ⟶ F.obj :=
  idealSheafQuotientTowerUnit X K G.obj ≫ β.hom.hom

include hβ in
@[reassoc]
theorem boundedCandidateStages_square (n : ℕᵒᵖ) :
    (boundedCandidateStages β).app n ≫ α.hom.app n =
      a.hom ≫ (idealSheafQuotientUnit X (K ^ n.unop)).app H.obj := by
  have he := congrArg (fun f => f.hom.app n) hβ
  change β.hom.hom.app n ≫ α.hom.app n =
    (idealSheafQuotientFunctor X (K ^ n.unop)).map a.hom at he
  change (_ ≫ β.hom.hom.app n) ≫ α.hom.app n = _
  rw [Category.assoc, he]
  exact ((idealSheafQuotientUnit X (K ^ n.unop)).naturality a.hom).symm

/-- The specified algebraic map and formal isomorphism give a map into the
original global reconstruction pullback. -/
def boundedCandidateLift : G.obj ⟶ reconstructionPullback α :=
  reconstructionLift α a.hom (boundedCandidateStages β)
    (boundedCandidateStages_square α a β hβ)

@[reassoc (attr := simp)]
theorem boundedCandidateLift_toTarget :
    boundedCandidateLift α a β hβ ≫ reconstructionToTarget α = a.hom :=
  reconstructionLift_toTarget _ _ _ _

@[reassoc (attr := simp)]
theorem boundedCandidateLift_toStage (n : ℕᵒᵖ) :
    boundedCandidateLift α a β hβ ≫ reconstructionToStage α n =
      (boundedCandidateStages β).app n :=
  reconstructionLift_toStage _ _ _ _ n

/-- Bounded ordinary kernels force actual monicity into the original global
ambient, using finite-stage detection on actual affine charts. -/
theorem boundedCandidateLift_mono_of_affineCover
    {ι : Type v} (B : ι → CommRingCat.{u}) [∀ i, IsNoetherianRing (B i)]
    (p : ∀ i, Spec (B i) ⟶ X) [∀ i, IsOpenImmersion (p i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Spec (B i)), p i y = x)
    (t : ℕ) (hk : killedByIdealSheaf (K ^ t) (kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (cokernel a.hom)) :
    Mono (boundedCandidateLift α a β hβ) := by
  constructor
  intro M f g he
  apply reconstructionHom_ext_of_openCover (fun i => Spec (B i)) p hcover
  intro i
  have hb := openReconstructionCandidate_bounds (p i) a t hk hc
  let s := boundedCandidateLift α a β hβ
  have hm : Mono ((pullback (p i)).map s) := by
    obtain ⟨n, hn⟩ := affineCandidateStages_jointly_monic
      ((coherentPullback (p i)).map a) (openReconstructionCandidateIso (p i) β) t hb.1
    let b : (pullback (p i)).obj (reconstructionPullback α) ⟶
        ((coherentPullback (p i)).obj H).obj :=
      (pullback (p i)).map (reconstructionToTarget α)
    let c : (pullback (p i)).obj (reconstructionPullback α) ⟶
        ((openIdealPullbackFunctor (p i) K).obj F).obj.obj (op n) :=
      (pullback (p i)).map (reconstructionToStage α (op n))
    apply @mono_of_mono_fac _ _ _ _ _ (prod.lift b c) ((pullback (p i)).map s) _ hn
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst]
      exact ((pullback (p i)).map_comp s (reconstructionToTarget α)).symm.trans
        (congrArg ((pullback (p i)).map) (boundedCandidateLift_toTarget α a β hβ))
    · simp only [Category.assoc, prod.lift_snd]
      exact ((pullback (p i)).map_comp s (reconstructionToStage α (op n))).symm.trans
        ((congrArg ((pullback (p i)).map) (boundedCandidateLift_toStage α a β hβ (op n))).trans
          (openReconstructionCandidateIso_stage (p i) β n).symm)
  have : Mono ((pullback (p i)).map s) := hm
  have hp : (pullback (p i)).map f = (pullback (p i)).map g := by
    apply (cancel_mono ((pullback (p i)).map s)).mp
    simpa only [← Functor.map_comp] using congrArg ((pullback (p i)).map) he
  apply (cancel_mono ((restrictFunctorIsoPullback (p i)).hom.app G.obj)).mp
  rw [(restrictFunctorIsoPullback (p i)).hom.naturality,
    (restrictFunctorIsoPullback (p i)).hom.naturality, hp]

/-- Every locally Noetherian scheme has enough actual affine charts for the
original bounded candidate embedding to be monic. -/
theorem boundedCandidateLift_mono (t : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (cokernel a.hom)) :
    Mono (boundedCandidateLift α a β hβ) := by
  let U := X.affineOpenCover
  let (i : U.I₀) : IsNoetherianRing (U.X i) :=
    isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (U.f i))
  exact boundedCandidateLift_mono_of_affineCover α a β hβ U.X U.f
    U.openCover.exists_eq t hk hc

end AlgebraicGeometry.Scheme.Modules.Coherent
