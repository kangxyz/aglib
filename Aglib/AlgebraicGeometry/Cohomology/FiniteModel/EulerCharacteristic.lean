/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Fibers
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Fibers.EulerCharacteristic
public import Aglib.Algebra.Homology.EulerCharacteristic.Cohomology
public import Aglib.Algebra.Homology.EulerCharacteristic.Fiber

/-!
# Intrinsic fibre Euler characteristics on the same actual finite-cover model

The unchanged ordinary fibre dimensions have finite support by the actual
strict bounds of this same model. Their original intrinsic alternating sum
is therefore its native homological Euler characteristic, and is locally
constant by the finite-projective term theorem. No reducedness or additional
Noetherian hypothesis is imposed on the model-level comparison.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module AlgebraicGeometry
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}} [X.IsSeparated]
    {U : ι → X.Opens}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- The original fibre Euler characteristic is the native homological Euler
characteristic of the same actual scalar-extended model. The actual strict bounds
prove finite support, including in projective dimension zero. -/
theorem FiniteCechCohomologyModel.moduleFiberEulerChar_eq_homologyEulerChar
    (D : FiniteCechCohomologyModel R ι X f U M n) [M.IsQuasicoherent]
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (p : PrimeSpectrum R) :
    moduleFiberEulerChar f M p = HomologicalComplex.homologyEulerChar
      (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (.up ℤ)).obj D.complex) := by
  let : D.complex.IsStrictlyGE 0 := D.lowerBound
  let : D.complex.IsStrictlyLE (n : ℤ) := D.upperBound
  let K : CochainComplex (ModuleCat.{u} p.asIdeal.ResidueField) ℤ :=
    ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
      (.up ℤ)).obj D.complex
  have hvan (q : ℕ) (hq : n < q) : moduleFiberCohomologyDimension f M q p = 0 := by
    rw [D.fiberCohomologyDimension_eq_finrank hU hcover e hflat q p]
    let : Subsingleton (K.homology (q : ℤ)) :=
      ModuleCat.subsingleton_of_isZero (K.isZero_of_isLE (n : ℤ) (q : ℤ)
        (by exact_mod_cast hq))
    exact Module.finrank_zero_of_subsingleton
  rw [moduleFiberEulerChar_eq_sum_range f M p n hvan,
    K.homologyEulerChar_eq_sum_range n]
  apply Finset.sum_congr rfl
  intro q _
  rw [D.fiberCohomologyDimension_eq_finrank hU hcover e hflat q p]

/-- The intrinsic original fibre Euler characteristic is locally constant for the
displayed actual universal model, without additional Noetherian hypotheses on its data. -/
theorem FiniteCechCohomologyModel.isLocallyConstant_moduleFiberEulerChar
    (D : FiniteCechCohomologyModel R ι X f U M n) [M.IsQuasicoherent]
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) :
    IsLocallyConstant (moduleFiberEulerChar f M) := by
  let : D.complex.IsStrictlyGE 0 := D.lowerBound
  let : D.complex.IsStrictlyLE (n : ℤ) := D.upperBound
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  have he : moduleFiberEulerChar f M = fun p : PrimeSpectrum R =>
      HomologicalComplex.homologyEulerChar
        (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj D.complex) :=
    funext (D.moduleFiberEulerChar_eq_homologyEulerChar hU hcover e hflat)
  rw [he]
  exact D.complex.isLocallyConstant_homologyEulerChar_residueField_of_projective 0 (n : ℤ)

end AlgebraicGeometry.Scheme.Cohomology
