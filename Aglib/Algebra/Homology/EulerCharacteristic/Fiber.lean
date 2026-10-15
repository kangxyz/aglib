/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.EulerCharacteristic
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.RingTheory.Spectrum.Prime.FiberDimension.Flat

/-!
# Locally constant Euler characteristics of fibre complexes

For a bounded complex of finitely presented flat modules, the Euler
characteristic of its original scalar-extended residue-field homology is
locally constant. The comparison uses the native Euler characteristic,
the original termwise bounds, and the native algebra tensor product in
each degree. No Noetherianity or global freeness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module

namespace CochainComplex

universe u v

variable {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{max u v} R) ℤ)

/-- The termwise Euler characteristic of the original residue-field complex is locally
constant for a bounded complex of finitely presented flat modules. -/
theorem isLocallyConstant_eulerChar_residueField (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [∀ i, Module.FinitePresentation R (C.X i)] [∀ i, Module.Flat R (C.X i)] :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      HomologicalComplex.eulerChar
        (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj C)) := by
  classical
  have he : (fun p : PrimeSpectrum R =>
      HomologicalComplex.eulerChar
        (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj C)) = fun p =>
      ∑ i ∈ Finset.Icc a b, ((ComplexShape.up ℤ).χ i : ℤ) *
        (finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (C.X i)) : ℤ) := by
    funext p
    let F := ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
    let K : CochainComplex (ModuleCat.{max u v} p.asIdeal.ResidueField) ℤ :=
      (F.mapHomologicalComplex (.up ℤ)).obj C
    have hs : GradedObject.finrankSupport K.X ⊆ (Finset.Icc a b : Set ℤ) := by
      simpa only [Finset.coe_Icc] using K.finrankSupport_subset_Icc_of_bounds a b
    rw [K.eulerChar_eq_sum_finSet_of_finrankSupport_subset (Finset.Icc a b) hs]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact congrArg (fun n : ℕ => (n : ℤ))
      (ModuleCat.extendScalarsAlgebraObjIso R p.asIdeal.ResidueField
        (C.X i)).toLinearEquiv.finrank_eq
  rw [he]
  have hs (s : Finset ℤ) : IsLocallyConstant (fun p : PrimeSpectrum R =>
      ∑ i ∈ s, ((ComplexShape.up ℤ).χ i : ℤ) *
        (finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (C.X i)) : ℤ)) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty, Function.const_def] using
        IsLocallyConstant.const (X := PrimeSpectrum R) (0 : ℤ)
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi, Function.comp_def] using
        ((Module.isLocallyConstant_finrank_fiber R (C.X i)).comp
          (fun n : ℕ => ((ComplexShape.up ℤ).χ i : ℤ) * (n : ℤ))).comp₂ ih (· + ·)
  exact hs (Finset.Icc a b)

/-- The homological Euler characteristic of the original residue-field complex is locally
constant for a bounded complex of finitely presented flat modules. -/
theorem isLocallyConstant_homologyEulerChar_residueField (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [∀ i, Module.FinitePresentation R (C.X i)] [∀ i, Module.Flat R (C.X i)] :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      HomologicalComplex.homologyEulerChar
        (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj C)) := by
  have he : (fun p : PrimeSpectrum R =>
      HomologicalComplex.homologyEulerChar
        (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj C)) = fun p =>
      HomologicalComplex.eulerChar
        (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj C) := by
    funext p
    let F := ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
    let K : CochainComplex (ModuleCat.{max u v} p.asIdeal.ResidueField) ℤ :=
      (F.mapHomologicalComplex (.up ℤ)).obj C
    let : ∀ i, Module.Finite p.asIdeal.ResidueField (K.X i) := fun i =>
      ModuleCat.finite_extendScalars (algebraMap R p.asIdeal.ResidueField) (C.X i)
    exact K.homologyEulerChar_eq_eulerChar a b
  rw [he]
  exact C.isLocallyConstant_eulerChar_residueField a b

/-- In particular, the original homological Euler characteristic is locally constant
for a bounded complex of finite projective modules. -/
theorem isLocallyConstant_homologyEulerChar_residueField_of_projective (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Projective R (C.X i)] :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      HomologicalComplex.homologyEulerChar
        (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj C)) := by
  let : ∀ i, Module.FinitePresentation R (C.X i) := fun i =>
    Module.finitePresentation_of_projective R (C.X i)
  exact C.isLocallyConstant_homologyEulerChar_residueField a b

end CochainComplex
