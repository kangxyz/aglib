/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Constants
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.Polynomial

/-!
# The literal global functions of polynomial projective space

For any commutative coefficient ring and a finite nonempty coordinate type,
the original structural coefficient map is bijective. The resulting ring
equivalence has that exact forward map. No field or nontriviality premise is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (I : Type u)

private theorem zeroSection_to_structuralCoefficient (r : R) :
    ((twistingZeroToUnit R I).val.app (op ⊤)
        (homogeneousSection R I 0 (toHomogeneousSubmoduleZero R I r)) :
      Γ(ProjectiveSpace R I, ⊤)) =
    ((toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r := by
  let P := ProjectiveSpace R I
  let M := SheafOfModules.unit P.ringCatSheaf
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.val.presheaf, M.isSheaf⟩
    (coordinateOpen R I) ⊤ (fun _ => homOfLE le_top)
    (by rw [iSup_coordinateOpen_eq_top])
  intro i
  change sectionRestrict P le_top
      ((twistingZeroToUnit R I).val.app (op ⊤)
        (homogeneousSection R I 0 (toHomogeneousSubmoduleZero R I r))) =
    sectionRestrict P le_top
      (((toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r)
  have hnat := PresheafOfModules.naturality_apply (twistingZeroToUnit R I).val
    (homOfLE (show coordinateOpen R I i ≤ ⊤ from le_top)).op
    (homogeneousSection R I 0 (toHomogeneousSubmoduleZero R I r))
  calc
    _ = (twistingZeroToUnit R I).val.app (op (coordinateOpen R I i))
        ((twistingSheaf R I 0).val.map (homOfLE le_top).op
          (homogeneousSection R I 0 (toHomogeneousSubmoduleZero R I r))) := hnat.symm
    _ = twistingSectionsEquiv R I 0 i le_rfl
        ((twistingSheaf R I 0).val.map (homOfLE le_top).op
          (homogeneousSection R I 0 (toHomogeneousSubmoduleZero R I r))) :=
      twistingZeroToUnit_app R I i le_rfl _
    _ = homogeneousChartSection R I 0 (toHomogeneousSubmoduleZero R I r) i :=
      homogeneousSection_local R I 0 (toHomogeneousSubmoduleZero R I r) i
    _ = (Proj.awayToSection (homogeneousSubmodule I R) (MvPolynomial.X i)).hom
        (coordinateRingCoefficient R I i r) := rfl
    _ = _ := (constant_restriction R I (MvPolynomial.X i)
      (isHomogeneous_X R i) Nat.zero_lt_one r).symm

/-- The original structural coefficient map gives every actual global function,
uniquely, on finite nonempty polynomial projective space. -/
theorem globalFunctionsCoefficient_bijective [Finite I] [Nonempty I] :
    Function.Bijective
      ((toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  classical
  let := Fintype.ofFinite I
  let j : I := Classical.choice (inferInstance : Nonempty I)
  let α : R →+* Γ(ProjectiveSpace R I, ⊤) :=
    (toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := Module.compHom Γ(twistingSheaf R I 0, ⊤) α
  have hC : Function.Bijective (toHomogeneousSubmoduleZero R I) :=
    (homogeneousSubmoduleZeroEquiv R I).symm.bijective
  have hS : Function.Bijective (homogeneousSection R I 0) := by
    have he : (fun p => Scheme.Cohomology.homogeneousSectionLinearEquiv R I j 0 p) =
        homogeneousSection R I 0 := by
      funext p
      exact Scheme.Cohomology.homogeneousSectionLinearEquiv_apply R I j 0 p
    rw [← he]
    exact (Scheme.Cohomology.homogeneousSectionLinearEquiv R I j 0).bijective
  have hZ : Function.Bijective
      (fun t : Γ(twistingSheaf R I 0, ⊤) =>
        ((twistingZeroToUnit R I).val.app (op ⊤) t : Γ(ProjectiveSpace R I, ⊤))) :=
    ((SheafOfModules.evaluation (ProjectiveSpace R I).ringCatSheaf (op ⊤)).mapIso
      (twistingZeroIso R I)).toLinearEquiv.bijective
  have h := hZ.comp (hS.comp hC)
  have hf : (fun r : R =>
      ((twistingZeroToUnit R I).val.app (op ⊤)
        (homogeneousSection R I 0 (toHomogeneousSubmoduleZero R I r)) :
          Γ(ProjectiveSpace R I, ⊤))) =
      (fun r : R => ((toSpec R I).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom) r) := by
    funext r
    exact zeroSection_to_structuralCoefficient R I r
  change Function.Bijective (fun r : R =>
    ((toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r)
  rw [← hf]
  exact h

/-- The actual global-functions ring equivalence, with the original structural
coefficient map as its literal forward ring homomorphism. -/
def globalFunctionsRingEquiv [Finite I] [Nonempty I] :
    R ≃+* Γ(ProjectiveSpace R I, ⊤) :=
  RingEquiv.ofBijective
    ((toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (globalFunctionsCoefficient_bijective R I)

@[simp]
theorem globalFunctionsRingEquiv_toRingHom [Finite I] [Nonempty I] :
    (globalFunctionsRingEquiv R I : R →+* Γ(ProjectiveSpace R I, ⊤)) =
      (toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom := rfl

@[simp]
theorem globalFunctionsRingEquiv_apply [Finite I] [Nonempty I] (r : R) :
    globalFunctionsRingEquiv R I r =
      ((toSpec R I).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r := rfl

/-- The inverse ring equivalence recovers the original coefficient exactly. -/
@[simp]
theorem globalFunctionsRingEquiv_symm_coefficient [Finite I] [Nonempty I] (r : R) :
    (globalFunctionsRingEquiv R I).symm
        ((toSpec R I).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) = r :=
  (globalFunctionsRingEquiv R I).symm_apply_apply r

/-- Applying the original structural coefficient map after the inverse recovers the
original global function. -/
@[simp]
theorem coefficient_globalFunctionsRingEquiv_symm [Finite I] [Nonempty I]
    (s : Γ(ProjectiveSpace R I, ⊤)) :
    (toSpec R I).appTop.hom
        ((Scheme.ΓSpecIso (.of R)).inv.hom ((globalFunctionsRingEquiv R I).symm s)) = s :=
  (globalFunctionsRingEquiv R I).apply_symm_apply s

end AlgebraicGeometry.ProjectiveSpace
