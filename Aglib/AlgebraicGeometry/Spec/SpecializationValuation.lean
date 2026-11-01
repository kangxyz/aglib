/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Original specializations realized by valuation spectra

The native local-hom factorization into a valuation subring of the original
residue field supplies a morphism to the original scheme. Both its generic
map and its closed point retain their original equations. No Noetherian or
DVR hypothesis, or alternate residue-field model, is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme
universe u

/-- Realize an original specialization using a valuation subring of the
original generizing point's residue field, retaining both original endpoints. -/
theorem exists_valuationSubring_of_specializes
    (X : Scheme.{u}) {x y : X} (h : x ⤳ y) :
    ∃ (A : ValuationSubring (X.residueField x)) (a : Spec (.of A) ⟶ X),
      Spec.algebraMap A (X.residueField x) ≫ a = X.fromSpecResidueField x ∧
      a (closedPoint A) = y := by
  let φ : X.presheaf.stalk y ⟶ X.residueField x :=
    X.presheaf.stalkSpecializes h ≫ X.residue x
  obtain ⟨A, hA, hlocal⟩ := exists_factor_valuationRing φ.hom
  let ψ : X.presheaf.stalk y ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (φ.hom.codRestrict A.toSubring hA)
  let a : Spec (.of A) ⟶ X := Spec.map ψ ≫ X.fromSpecStalk y
  refine ⟨A, a, ?_, ?_⟩
  · change Spec.algebraMap A (X.residueField x) ≫ Spec.map ψ ≫ X.fromSpecStalk y = _
    rw [← Spec.map_comp_assoc]
    change Spec.map (X.presheaf.stalkSpecializes h ≫ X.residue x) ≫
      X.fromSpecStalk y = X.fromSpecResidueField x
    rw [Spec.map_comp, Category.assoc, SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  · have he : Spec.map ψ (closedPoint A) = closedPoint (X.presheaf.stalk y) :=
      comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
    change X.fromSpecStalk y (Spec.map ψ (closedPoint A)) = y
    rw [he, X.fromSpecStalk_closedPoint]

end AlgebraicGeometry.Scheme
