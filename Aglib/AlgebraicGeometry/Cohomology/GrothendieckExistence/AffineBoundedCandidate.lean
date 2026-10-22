/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedModule
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionNaturality
public import Aglib.RingTheory.AdicCompletion.BoundedReconstructionUnique

/-! # Original affine bounded candidates recover the same native pullback

The input retains the original algebraic target map, its bounded ordinary
defects, and its actual formal comparison square. An isomorphism of
completions alone is not a uniqueness hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H G : (Spec B).CoherentSheaf} (α : F ⟶ (completionFunctor (Spec B) K).obj H)
  (a : G ⟶ H) (β : (completionFunctor (Spec B) K).obj G ≅ F)
  (hβ : β.hom ≫ α = (completionFunctor (Spec B) K).map a)

/-- The original formal section module carries the completed coefficient-ring action. -/
local instance affineBoundedCandidateSectionsModule :
    Module (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineFormalSectionsModule
local instance affineBoundedCandidateSectionsScalarTower :
    IsScalarTower B (AdicCompletion (affineIdeal B K) B) F.affineFormalSections :=
  F.affineSections_isCompatibleSystem.sectionsScalarTower

/-- The specified formal isomorphism on the actual completed original module. -/
def affineCandidateCompletionEquiv :
    AdicCompletion (affineIdeal B K) (moduleSpecΓFunctor.obj G.obj) ≃ₗ[
      AdicCompletion (affineIdeal B K) B] F.affineFormalSections :=
  (affineCompletionSectionsEquiv B K G).trans (AdicSystem.affineFormalSectionsIso B K β)

include hβ in
/-- The specified formal square is exactly the original completed-linear
square needed by bounded candidate uniqueness. -/
theorem affineCandidateCompletionEquiv_square :
    (affineReconstructionMap α).comp (affineCandidateCompletionEquiv β).toLinearMap =
      AdicCompletion.map (affineIdeal B K) (moduleSpecΓFunctor.map a.hom).hom := by
  apply LinearMap.ext
  intro x
  apply (affineCompletionSectionsEquiv B K H).injective
  change (affineCompletionSectionsEquiv B K H)
      ((affineCompletionSectionsEquiv B K H).symm
        (AdicSystem.affineFormalSectionsMap α
          (AdicSystem.affineFormalSectionsMap β.hom
            (affineCompletionSectionsEquiv B K G x)))) = _
  rw [LinearEquiv.apply_symm_apply]
  have hs := congrArg (fun q => (AdicSystem.affineFormalSectionsFunctor B K).map q
    (affineCompletionSectionsEquiv B K G x)) hβ
  have ht := LinearMap.congr_fun (affineCompletionSectionsEquiv_naturality B K a) x
  exact hs.trans ht

/-- Every bounded actual algebraic candidate is canonically the original
finite affine reconstruction pullback. -/
def affineCandidatePullbackEquiv (t : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (CategoryTheory.Limits.kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (CategoryTheory.Limits.cokernel a.hom)) :
    moduleSpecΓFunctor.obj G.obj ≃ₗ[B] affineReconstructionModule α := by
  let : G.obj.IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B G.obj).mp G.property).1
  let : H.obj.IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).1
  let : Module.Finite B (moduleSpecΓFunctor.obj G.obj) :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B G.obj).mp G.property).2
  let : Module.Finite B (moduleSpecΓFunctor.obj H.obj) :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B H.obj).mp H.property).2
  exact AdicCompletion.candidatePullbackEquiv (affineIdeal B K)
    (affineReconstructionMap α) (moduleSpecΓFunctor.map a.hom).hom t
    (affineSections_kernel_bound a.hom K t hk)
    (affineSections_cokernel_bound a.hom K t hc)
    (affineCandidateCompletionEquiv β) (affineCandidateCompletionEquiv_square α a β hβ)

/-- The candidate equivalence retains the literal original algebraic target map. -/
@[simp]
theorem affineCandidatePullbackEquiv_toTarget (t : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (CategoryTheory.Limits.kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (CategoryTheory.Limits.cokernel a.hom))
    (x : moduleSpecΓFunctor.obj G.obj) :
    (affineCandidatePullbackEquiv α a β hβ t hk hc x).val.2 =
      moduleSpecΓFunctor.map a.hom x := by
  rfl

/-- The candidate equivalence retains every original formal-stage map,
including its actual algebraic quotient unit. -/
theorem affineCandidatePullbackEquiv_toStage (t : ℕ)
    (hk : killedByIdealSheaf (K ^ t) (CategoryTheory.Limits.kernel a.hom))
    (hc : killedByIdealSheaf (K ^ t) (CategoryTheory.Limits.cokernel a.hom))
    (x : moduleSpecΓFunctor.obj G.obj) (n : ℕ) :
    (affineCandidatePullbackEquiv α a β hβ t hk hc x).val.1.val (Opposite.op n) =
      moduleSpecΓFunctor.map (β.hom.hom.app (Opposite.op n))
        (affineCompletionUnit B K G n x) := by
  change (AdicSystem.affineFormalSectionsMap β.hom
    (affineCompletionSectionsEquiv B K G
      (AdicCompletion.of (affineIdeal B K) _ x))).val (Opposite.op n) = _
  rw [AdicSystem.affineFormalSectionsMap_apply, affineCompletionSectionsEquiv_of]
  rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
