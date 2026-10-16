/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator.Sections
public import Aglib.AlgebraicGeometry.Modules.Tensor.Linear

/-!
# Original twist tensor adjunction on pure sections

The original composition and tensor-unit maps retain the original twist
product on pure sections. These formulas supply normalization of the
original cancellation and Hom adjunction in subsequent consumers.
No cohomology or replacement equivalence is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original composition comparison carries the original nested pure section to
multiplication of the two twist factors and the unchanged coefficient section. -/
theorem twistingTensorCompIso_hom_section (a b : ℤ)
    (N : (ProjectiveSpace R ι).Modules) (U : (ProjectiveSpace R ι).Opens)
    (s : Γ(twistingSheaf R ι a, U)) (t : Γ(twistingSheaf R ι b, U)) (n : Γ(N, U)) :
    ((twistingTensorCompIso R ι a b).hom.app N).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj N) U s
            (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι b) N U t n)) =
      moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (a + b)) N U
        (twistingSectionMul R ι a b U s t) n := by
  have hc : ∀ x : ProjectiveSpace R ι, ∃ (i : ι) (y : (coordinateOpen R ι i).toScheme),
      (coordinateOpen R ι i).ι y = x := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ iSup (coordinateOpen R ι) by rw [iSup_coordinateOpen_eq_top]; trivial)
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  have ha := moduleLineTensorAssociator_hom_section (X := ProjectiveSpace R ι)
    (twistingSheaf R ι a) (twistingSheaf R ι b)
    (fun i => (coordinateOpen R ι i).toScheme) (fun i => (coordinateOpen R ι i).ι) hc
    (twistingRestrictUnitIso R ι a) (twistingRestrictUnitIso R ι b) N U s t n
  let e := moduleLineTensorAssociator (X := ProjectiveSpace R ι)
    (twistingSheaf R ι a) (twistingSheaf R ι b)
    (fun i => (coordinateOpen R ι i).toScheme) (fun i => (coordinateOpen R ι i).ι) hc
    (twistingRestrictUnitIso R ι a) (twistingRestrictUnitIso R ι b)
  change ((moduleTensorCoefficientMap (ProjectiveSpace R ι)
      (twistingTensorIso R ι a b).hom).app N).val.app (op U)
      ((e.hom.app N).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj N) U s
            (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι b) N U t n))) = _
  erw [ha]
  erw [moduleTensorCoefficientMap_section (X := ProjectiveSpace R ι)
    (twistingTensorIso R ι a b).hom N U
    (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
      (twistingSheaf R ι b) U s t) n]
  rw [twistingTensorIso_hom]
  exact congrArg (fun w => moduleTensorSection (ProjectiveSpace R ι)
    (twistingSheaf R ι (a + b)) N U w n) (twistingTensorMap_section R ι a b U s t)

/-- The original functor equality map acts only by the same original twist equality map
on the first pure-tensor factor. -/
theorem twistingTensorFunctorCongr_hom_section {c d : ℤ} (h : c = d)
    (N : (ProjectiveSpace R ι).Modules) (U : (ProjectiveSpace R ι).Opens)
    (s : Γ(twistingSheaf R ι c, U)) (n : Γ(N, U)) :
    ((eqToIso (congrArg (fun k => moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom.app N).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι c) N U s n) =
      moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) N U
        ((eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U) s) n := by
  cases h
  rfl

/-- The original zero-twist tensor comparison is the original zero-frame coefficient
acting on the unchanged coefficient section. -/
theorem twistingTensorZeroIso_hom_section
    (N : (ProjectiveSpace R ι).Modules) (U : (ProjectiveSpace R ι).Opens)
    (s : Γ(twistingSheaf R ι 0, U)) (n : Γ(N, U)) :
    ((twistingTensorZeroIso R ι).hom.app N).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι 0) N U s n) =
      ((SheafOfModulesOfCommRing.tensorLeftUnitIso (ProjectiveSpace R ι).sheaf).hom.app
        N).val.app (op U)
          (moduleTensorSection (ProjectiveSpace R ι)
            (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf) N U
              ((twistingZeroIso R ι).hom.val.app (op U) s) n) := by
  dsimp only [twistingTensorZeroIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapIso_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change ((SheafOfModulesOfCommRing.tensorLeftUnitIso (ProjectiveSpace R ι).sheaf).hom.app
      N).val.app (op U)
      (((moduleTensorCoefficientMap (ProjectiveSpace R ι) (twistingZeroIso R ι).hom).app
        N).val.app (op U)
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι 0) N U s n)) = _
  erw [moduleTensorCoefficientMap_section (X := ProjectiveSpace R ι)
    (twistingZeroIso R ι).hom N U s n]
  rfl

/-- The original twist tensor-unit comparison is literal local scalar multiplication. -/
theorem twistingTensorUnitIso_hom_section (a : ℤ) (U : (ProjectiveSpace R ι).Opens)
    (s : Γ(twistingSheaf R ι a, U)) (r : Γ(ProjectiveSpace R ι, U)) :
    (twistingTensorUnitIso R ι a).hom.val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι a)
          (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf) U s r) = r • s :=
  tensorRightUnitIso_hom_section (ProjectiveSpace R ι) (twistingSheaf R ι a) U s r

end AlgebraicGeometry.ProjectiveSpace
