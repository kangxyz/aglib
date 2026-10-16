/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Homology
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Projection

/-!
# Original coefficient projections and actual weight homology components

The component of the native weight homology decomposition is precisely the
actual homology map of the original Laurent coefficient chain projection.
The proof uses the original monomial inclusions, their proved retractions
and the literal native dependent-sum single generators.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory HomologicalComplex AlgebraicTopology

universe u v

namespace MvPolynomial

variable {ι : Type v} [Finite ι] (R : Type u) [CommRing R]

/-- A component of the actual homology decomposition is the unchanged
homology map of the literal original Laurent coefficient projection. -/
theorem coordinateLaurentTupleHomologyWeightsEquiv_apply_eq_projection (d : ℤ) (q : ℕ)
    (x : (coordinateLaurentTupleComplex (ι := ι) R d).homology q)
    (e : coordinateLaurentWeight (ι := ι) d) :
    coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d q x e =
      homologyMap (coordinateLaurentWeightComplexProjection R d e) q x := by
  classical
  let E := coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d q
  have hinv (e' : coordinateLaurentWeight (ι := ι) d)
      (y : (RelativeSimplex.complex R (coordinateNegativeSupport e'.val)).homology q) :
      E.symm (DFinsupp.single e' y) =
        homologyMap (coordinateLaurentWeightComplexMap R d e') q y := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (coordinateLaurentTupleHomologyWeightsEquiv_homologyMap R d q e' y).symm
  let L := (homologyMap (coordinateLaurentWeightComplexProjection R d e) q).hom.comp
    E.symm.toLinearMap
  have hL : L = DFinsupp.lapply e := by
    apply DFinsupp.lhom_ext
    intro e' y
    change homologyMap (coordinateLaurentWeightComplexProjection R d e) q
      (E.symm (DFinsupp.single e' y)) =
        (DFinsupp.single e' y : Π₀ e : coordinateLaurentWeight (ι := ι) d,
          (RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology q) e
    rw [hinv]
    change (homologyMap (coordinateLaurentWeightComplexMap R d e') q ≫
      homologyMap (coordinateLaurentWeightComplexProjection R d e) q) y = _
    rw [← homologyMap_comp]
    by_cases he : e' = e
    · subst e'
      rw [coordinateLaurentWeightComplexMap_projection, homologyMap_id]
      simp
    · rw [coordinateLaurentWeightComplexMap_projection_of_ne R d e e' he, homologyMap_zero]
      simp [DFinsupp.single_eq_of_ne (Ne.symm he)]
  have hx := LinearMap.congr_fun hL (E x)
  change homologyMap (coordinateLaurentWeightComplexProjection R d e) q (E.symm (E x)) = E x e at hx
  rw [LinearEquiv.symm_apply_apply] at hx
  exact hx.symm

end MvPolynomial
