/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Tensor equivalences of the original projective twists

The original sheafified two-line associator, standard frame trivializations and original
twist multiplication identify successive twist tensor functors. Tensoring by `O(d)` is
therefore an actual equivalence with inverse tensoring by `O(-d)`. Native adjointification
supplies its triangle equation while preserving the two original functors.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original local frame, transported to native module restriction on the open scheme. -/
def twistingRestrictUnitIso (d : ℤ) (i : ι) :
    (twistingSheaf R ι d).restrict (coordinateOpen R ι i).ι ≅
      SheafOfModules.unit (coordinateOpen R ι i).toScheme.ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv (coordinateOpen R ι i)).app
      (twistingSheaf R ι d)).symm ≪≫
    (Scheme.Modules.overEquiv (coordinateOpen R ι i)).functor.mapIso
      (twistingLocalIso R ι d i) ≪≫
    (Scheme.Modules.overFunctorEquiv (coordinateOpen R ι i)).app
      (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso (coordinateOpen R ι i).ι

/-- Original twist multiplication and the actual line associator give the sum-twist functor. -/
def twistingTensorCompIso (a b : ℤ) :
    moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b) ⋙
        moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a) ≅
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (a + b)) :=
  moduleLineTensorAssociator (twistingSheaf R ι a) (twistingSheaf R ι b)
      (fun i => (coordinateOpen R ι i).toScheme) (fun i => (coordinateOpen R ι i).ι)
      (by
        intro x
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup (coordinateOpen R ι) by
          rw [iSup_coordinateOpen_eq_top]
          trivial)
        exact ⟨i, ⟨x, hi⟩, rfl⟩)
      (twistingRestrictUnitIso R ι a) (twistingRestrictUnitIso R ι b) ≪≫
    (SheafOfModulesOfCommRing.tensorFunctor (ProjectiveSpace R ι).sheaf).mapIso
      (twistingTensorIso R ι a b)

/-- The zero-twist tensor functor is the identity through the original unit maps. -/
def twistingTensorZeroIso :
    moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι 0) ≅
      𝟭 (ProjectiveSpace R ι).Modules :=
  (SheafOfModulesOfCommRing.tensorFunctor (ProjectiveSpace R ι).sheaf).mapIso
      (twistingZeroIso R ι) ≪≫
    SheafOfModulesOfCommRing.tensorLeftUnitIso (ProjectiveSpace R ι).sheaf

/-- Opposite twist tensor functors cancel through original multiplication and unit maps. -/
def twistingTensorCancelIso (a b : ℤ) (h : a + b = 0) :
    moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b) ⋙
        moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a) ≅
      𝟭 (ProjectiveSpace R ι).Modules :=
  twistingTensorCompIso R ι a b ≪≫
    eqToIso (congrArg (fun d =>
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)) h) ≪≫
    twistingTensorZeroIso R ι

/-- Tensoring by the actual integer twist is a native equivalence. Adjointification changes
only the unit constraint; the original tensor functor and opposite-twist inverse remain. -/
def twistingTensorEquivalence (d : ℤ) :
    (ProjectiveSpace R ι).Modules ≌ (ProjectiveSpace R ι).Modules :=
  CategoryTheory.Equivalence.mk
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d))
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-d)))
    (twistingTensorCancelIso R ι (-d) d (by omega)).symm
    (twistingTensorCancelIso R ι d (-d) (by omega))

/-- The forward functor is exactly tensoring by the original twist. -/
theorem twistingTensorEquivalence_functor (d : ℤ) :
    (twistingTensorEquivalence R ι d).functor =
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d) := rfl

/-- The inverse functor is exactly tensoring by the original opposite twist. -/
theorem twistingTensorEquivalence_inverse (d : ℤ) :
    (twistingTensorEquivalence R ι d).inverse =
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (-d)) := rfl

instance twistingTensorFunctor_isEquivalence (d : ℤ) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).IsEquivalence :=
  inferInstanceAs (twistingTensorEquivalence R ι d).functor.IsEquivalence

/-- Tensoring the structure module by a twist is that original twist, through the actual
sheafified right unitor and counit. -/
def twistingTensorUnitIso (d : ℤ) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj
        (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf) ≅ twistingSheaf R ι d :=
  (SheafOfModulesOfCommRing.tensorRightUnitIso (ProjectiveSpace R ι).sheaf).app
    (twistingSheaf R ι d)

end AlgebraicGeometry.ProjectiveSpace
