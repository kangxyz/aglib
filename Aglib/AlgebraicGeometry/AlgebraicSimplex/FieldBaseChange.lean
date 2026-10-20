/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of the literal field-coefficient extension on simplex rings

The eliminated-coordinate chart is proved to intertwine the actual coefficient
map. Polynomial base change is the existing tensor pushout, so arbitrary field
extension gives flatness of the original simplex map, not a substitute map.
-/

@[expose] public section



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace AlgebraicGeometry.AlgebraicSimplex
universe u
variable {K L : Type u} [Field K] [Field L]

/-- The actual polynomial chart commutes with the literal coefficient map. -/
theorem polynomial_coefficientMap (f : K →+* L) (j : ℕ) :
    (toPolynomial L j).toRingHom.comp (coefficientMap f j) =
      (MvPolynomial.map f).comp (toPolynomial K j).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    change toPolynomial L j (coefficientMap f j
      (algebraMap K (CoordinateRing K j) a)) =
      MvPolynomial.map f (toPolynomial K j (algebraMap K (CoordinateRing K j) a))
    rw [coefficientMap_algebraMap, AlgHom.commutes, AlgHom.commutes]
    simp
  · intro i
    change toPolynomial L j (coefficientMap f j (coordinate K j i)) =
      MvPolynomial.map f (toPolynomial K j (coordinate K j i))
    rw [coefficientMap_coordinate]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp

/-- Polynomial coefficient extension is the actual tensor pushout of a field map. -/
theorem polynomial_map_flat (f : K →+* L) (j : ℕ) :
    (MvPolynomial.map (σ := Fin j) f).Flat := by
  let := f.toAlgebra
  have h : Module.Flat (MvPolynomial (Fin j) K) (MvPolynomial (Fin j) L) :=
    Module.Flat.of_linearEquiv
      (Algebra.IsPushout.equiv K (MvPolynomial (Fin j) K) L
        (MvPolynomial (Fin j) L)).symm.toLinearEquiv
  change (algebraMap (MvPolynomial (Fin j) K) (MvPolynomial (Fin j) L)).Flat
  exact RingHom.flat_algebraMap_iff.mpr h

/-- Flatness is transported back through the PROVED actual polynomial charts. -/
theorem coefficientMap_flat (f : K →+* L) (j : ℕ) : (coefficientMap f j).Flat := by
  have heq : coefficientMap f j =
      (polynomialEquiv L j).symm.toRingEquiv.toRingHom.comp
        ((MvPolynomial.map f).comp (polynomialEquiv K j).toRingEquiv.toRingHom) := by
    apply RingHom.ext
    intro x
    apply (polynomialEquiv L j).injective
    change polynomialEquiv L j (coefficientMap f j x) =
      polynomialEquiv L j ((polynomialEquiv L j).symm (MvPolynomial.map f (polynomialEquiv K j x)))
    rw [AlgEquiv.apply_symm_apply]
    exact DFunLike.congr_fun (polynomial_coefficientMap f j) x
  rw [heq]
  exact ((RingHom.Flat.of_bijective (polynomialEquiv K j).bijective).comp
    (polynomial_map_flat f j)).comp (RingHom.Flat.of_bijective (polynomialEquiv L j).symm.bijective)

end AlgebraicGeometry.AlgebraicSimplex

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AlgebraicSimplex/FieldBaseChange.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 0d9b251c12a39b56254adef25df1c7cd2a45d559c75b87dfc68e04d872a3471a.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
