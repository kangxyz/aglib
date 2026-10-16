/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LaurentComparison
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.UniversalTensor
public import Aglib.Algebra.Homology.Flat.Truncation

/-!
# The original bounded flat Cech models of all integer twists

The unchanged structural-ring Cech terms of projective twists are free through their
original Laurent coordinates. Integer zero extension retains their flatness. The actual
universal tensor tail then proves flatness of the native good truncation, including its
original boundary cycles. The source model and scalar action are unchanged.

Every commutative base ring and integer twist is allowed. No Noetherianity or relative-flat
coefficient input is imposed, and no K-flatness of the unbounded full Cech complex is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace
open MvPolynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Finite ι]

/-- Every original full-tuple Cech term of an integer projective twist is free over the
original structural base ring, with its unchanged Laurent section comparison. -/
theorem twistingCechComplex_free_X (d : ℤ) (q : ℕ) :
    Module.Free R ((moduleCechComplex (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheaf R ι d) (coordinateOpen R ι)).X q) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : ∀ a : Fin (q + 1) → ι,
      Module.Free R (coordinateGrading R (coordinateTupleSet a) d) := fun a =>
    Module.Free.of_equiv (coordinateGradeEquivFinsupp R (coordinateTupleSet a) d).symm
  let : Module.Free R ((coordinateLaurentTupleComplex (ι := ι) R d).X q) := by
    change Module.Free R (∀ a : Fin (q + 1) → ι,
      coordinateGrading R (coordinateTupleSet a) d)
    infer_instance
  exact Module.Free.of_equiv (twistingCechLaurentTermIso R ι d q).symm.toLinearEquiv

/-- The native integer extension of the same Cech complex has flat terms; its negative
terms are the original zero objects. -/
theorem twistingCechIntComplex_flat_X (d : ℤ) (q : ℤ) :
    Module.Flat R ((moduleCechIntComplex (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (coordinateOpen R ι) (twistingSheaf R ι d)).X q) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  by_cases hq : 0 ≤ q
  · let := twistingCechComplex_free_X R ι d q.toNat
    have h : Module.Flat R ((moduleCechComplex P α
      (twistingSheaf R ι d) (coordinateOpen R ι)).X q.toNat) := inferInstance
    exact (Module.Flat.equiv_iff
      ((moduleCechComplex P α (twistingSheaf R ι d) (coordinateOpen R ι)).extendXIso
        ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hq)).toLinearEquiv).mpr h
  · have hz : IsZero ((moduleCechIntComplex P α (coordinateOpen R ι)
        (twistingSheaf R ι d)).X q) :=
      (moduleCechComplex P α (twistingSheaf R ι d) (coordinateOpen R ι)).isZero_extend_X
        ComplexShape.embeddingUpNat q (by
          intro i hi
          change (i : ℤ) = q at hi
          omega)
    let := ModuleCat.subsingleton_of_isZero hz
    infer_instance

/-- The same bounded native good truncation is termwise flat, including its actual
cutoff cycles, by the proved universal tensor exactness of the following degree. -/
theorem twistingFiniteCechComplex_flat_X (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (q : ℤ) :
    Module.Flat R ((moduleFiniteCechComplex (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (coordinateOpen R ι) (twistingSheaf R ι d) n).X q) := by
  let P := ProjectiveSpace R ι
  let α : R →+* Γ(P, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let K := moduleCechIntComplex P α (coordinateOpen R ι) (twistingSheaf R ι d)
  let (i : ℤ) : Module.Flat R (K.X i) := twistingCechIntComplex_flat_X R ι d i
  exact K.flat_truncLE_X_of_universally_lTensor_exact (n : ℤ)
    (moduleCechIntComplex_universally_lTensor_exact (toSpec R ι) (twistingSheaf R ι d)
      (coordinateOpen R ι) n e (isAffineOpen_coordinateOpen R ι)
        (iSup_coordinateOpen_eq_top R ι)) q

end AlgebraicGeometry.Scheme.Cohomology
