/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Single
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# The original one-element quotient and the principal ideal quotient

The scalar image on the ring is exactly its principal ideal. Transport the
original module quotient to the actual ring ideal quotient, retaining both
quotient representatives and the original augmentation. No regularity or
Noetherian hypothesis enters this comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] (a : R)

/-- The actual scalar boundary on the ring has precisely the principal ideal as its image. -/
theorem singleScalarRange_eq_span :
    LinearMap.range (LinearMap.lsmul R R a) = Ideal.span {a} := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact Ideal.mul_mem_right r _ (Ideal.subset_span (Set.mem_singleton a))
  · intro hx
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hx
    refine ⟨r, ?_⟩
    simpa only [LinearMap.lsmul_apply, smul_eq_mul] using hr.symm

/-- The original scalar-image module quotient is the actual principal ideal quotient. -/
def singleQuotientIdealLinearEquiv :
    SingleQuotient R a ≃ₗ[R] R ⧸ Ideal.span {a} :=
  Submodule.quotEquivOfEq _ _ (singleScalarRange_eq_span a)

/-- The quotient comparison retains every original ring representative. -/
@[simp]
theorem singleQuotientIdealLinearEquiv_apply_mk (r : R) :
    singleQuotientIdealLinearEquiv a (Submodule.Quotient.mk r) =
      Ideal.Quotient.mk (Ideal.span {a}) r :=
  Submodule.quotEquivOfEq_mk _ _ _ r

/-- The inverse comparison retains the same representative in the original module quotient. -/
@[simp]
theorem singleQuotientIdealLinearEquiv_symm_apply_mk (r : R) :
    (singleQuotientIdealLinearEquiv a).symm (Ideal.Quotient.mk (Ideal.span {a}) r) =
      Submodule.Quotient.mk r := by
  apply (singleQuotientIdealLinearEquiv a).injective
  simp only [LinearEquiv.apply_symm_apply, singleQuotientIdealLinearEquiv_apply_mk]

/-- The original augmentation becomes the literal ideal quotient projection. -/
@[reassoc]
theorem singleAugmentationMap_comp_ideal :
    singleAugmentationMap R a ≫ (singleQuotientIdealLinearEquiv a).toModuleIso.hom =
      ModuleCat.ofHom (Ideal.span {a}).mkQ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact singleQuotientIdealLinearEquiv_apply_mk a


variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The original scalar-image quotient is killed by its defining scalar. -/
theorem singleQuotientIsTorsionBy : Module.IsTorsionBy R (SingleQuotient M a) a :=
  (Module.isTorsionBy_quotient_iff (LinearMap.range (LinearMap.lsmul R M a)) a).mpr
    (fun x => ⟨x, rfl⟩)

/-- The native principal quotient-ring action on the original coefficient quotient.
The instance is explicit to retain its compatibility with the original R-action. -/
@[instance_reducible]
def singleQuotientModule : Module (R ⧸ Ideal.span {a}) (SingleQuotient M a) :=
  (singleQuotientIsTorsionBy a M).module

/-- A ring representative acts by the original scalar on the original quotient. -/
@[simp]
theorem singleQuotientModule_mk_smul (r : R) (x : SingleQuotient M a) :
    letI := singleQuotientModule a M
    Ideal.Quotient.mk (Ideal.span {a}) r • x = r • x :=
  Module.IsTorsionBy.mk_smul (singleQuotientIsTorsionBy a M) r x

/-- The unchanged principal quotient comparison is linear over the actual quotient ring. -/
def singleQuotientIdealQuotientLinearEquiv :
    letI := singleQuotientModule a R
    SingleQuotient R a ≃ₗ[R ⧸ Ideal.span {a}] R ⧸ Ideal.span {a} := by
  letI := singleQuotientModule a R
  exact {
    __ := (singleQuotientIdealLinearEquiv a).toAddEquiv
    map_smul' := by
      intro b x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [singleQuotientModule_mk_smul]
      exact (singleQuotientIdealLinearEquiv a).map_smul r x }

/-- Quotient-linearity retains the original additive comparison. -/
@[simp]
theorem singleQuotientIdealQuotientLinearEquiv_toAddEquiv :
    letI := singleQuotientModule a R
    (singleQuotientIdealQuotientLinearEquiv a).toAddEquiv =
      (singleQuotientIdealLinearEquiv a).toAddEquiv := rfl

/-- The quotient-linear comparison retains every original ring representative. -/
@[simp]
theorem singleQuotientIdealQuotientLinearEquiv_apply_mk (r : R) :
    singleQuotientIdealQuotientLinearEquiv a (Submodule.Quotient.mk r) =
      Ideal.Quotient.mk (Ideal.span {a}) r := singleQuotientIdealLinearEquiv_apply_mk a r

end ChainComplex.Koszul
