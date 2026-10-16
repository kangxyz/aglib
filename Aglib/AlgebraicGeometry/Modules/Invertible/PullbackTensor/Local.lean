/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Restriction

/-!
# Tensor pullback for rank-one sheaves and the Picard homomorphism

The canonical comparison and its general restriction/unit laws have lower module
owners. This leaf retains the actual locally-rank-one and line-bundle consequences,
including the additive pullback on the same Picard groups.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
universe u
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- The canonical tensor comparison is invertible when the first factor is locally rank one. -/
theorem pullbackTensorMap_isIso (M N : Y.Modules) (hM : IsLocallyRankOne Y M) :
    IsIso (pullbackTensorMap f M N) := by
  apply isIso_of_local_restrict
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit M).mp hM (f.base x)
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  haveI := pullbackTensorMap_isIso_of_trivial_left (f ∣_ U)
    ((Scheme.Modules.restrictFunctor U.ι).obj M)
    ((Scheme.Modules.restrictFunctor U.ι).obj N) e
  haveI := restrictTensorMap_isIso Y U M N
  haveI := restrictTensorMap_isIso X (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N)
  haveI : IsIso (tensorSheafMap (f ⁻¹ᵁ U).toScheme
      ((localPullbackIso f U).inv.app M) ((localPullbackIso f U).inv.app N)) :=
    (tensorSheafIso (f ⁻¹ᵁ U).toScheme ((localPullbackIso f U).app M).symm
      ((localPullbackIso f U).app N).symm).isIso_hom
  haveI : IsIso ((Scheme.Modules.pullback (f ∣_ U)).map (restrictTensorMap Y U M N) ≫
      (localPullbackIso f U).inv.app (show Y.Modules from tensorSheaf Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackTensorMap f M N)) := by
    rw [pullbackTensorMap_restrict]
    infer_instance
  haveI := IsIso.of_isIso_comp_left
    ((Scheme.Modules.pullback (f ∣_ U)).map (restrictTensorMap Y U M N))
    ((localPullbackIso f U).inv.app (show Y.Modules from tensorSheaf Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackTensorMap f M N))
  exact IsIso.of_isIso_comp_left
    ((localPullbackIso f U).inv.app (show Y.Modules from tensorSheaf Y M N))
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackTensorMap f M N))

/-- The actual canonical pullback comparison for line bundles, with no tensor-pullback premise. -/
def pullbackLineBundleTensorIso (L M : LineBundle Y) :
    (pullbackLineBundle f (tensorLineBundle Y L M)).val ≅
      (tensorLineBundle X (pullbackLineBundle f L) (pullbackLineBundle f M)).val := by
  haveI := pullbackTensorMap_isIso f L.val M.val L.property
  let e := asIso (pullbackTensorMap f L.val M.val)
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

@[simp] theorem pullbackLineBundleTensorIso_hom (L M : LineBundle Y) :
    (pullbackLineBundleTensorIso f L M).hom = pullbackTensorMap f L.val M.val := rfl

theorem pullbackClass_add (a b : PicardGroup Y) :
    pullbackClass f (a + b) = pullbackClass f a + pullbackClass f b := by
  induction a using Quotient.inductionOn with | h L =>
    induction b using Quotient.inductionOn with | h M =>
      exact Quotient.sound ⟨pullbackLineBundleTensorIso f L M⟩

/-- Pullback on the actual Picard groups, proved from open-local unit charts. -/
def pullbackHom : PicardGroup Y →+ PicardGroup X where
  toFun := pullbackClass f
  map_zero' := pullbackClass_zero f
  map_add' := pullbackClass_add f

@[simp] theorem pullbackHom_apply (a : PicardGroup Y) :
    pullbackHom f a = pullbackClass f a := rfl

theorem pullbackClass_neg (a : PicardGroup Y) : pullbackClass f (-a) = -pullbackClass f a :=
  map_neg (pullbackHom f) a

@[simp] theorem pullbackHom_id :
    pullbackHom (𝟙 X) = AddMonoidHom.id (PicardGroup X) := by
  ext a
  exact pullbackClass_id a

@[simp] theorem pullbackHom_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    pullbackHom (f ≫ g) = (pullbackHom f).comp (pullbackHom g) := by
  ext a
  exact pullbackClass_comp f g a
end AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
