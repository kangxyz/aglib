/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Coefficient automorphisms of simplex and Laurent coordinate rings

The original scalar automorphism and its inverse act on the actual coordinate
quotient. Laurent monomials keep their two ordered integer exponents. The forward
ring maps are the canonical coefficient maps, before any transport of ideals.

Extracted from the pure algebra prefix of
`R5Lab.Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ScalarTransport` at
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Its field hypothesis is
unnecessary for these constructions; the same proofs work over commutative rings.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.AlgebraicSimplex

universe u
variable {L : Type u} [CommRing L]

/-- Literal coefficient transport, with its inverse constructed from the
inverse field automorphism. -/
def coefficientEquiv (e : L ≃+* L) (d : ℕ) :
    AlgebraicSimplex.CoordinateRing L d ≃+* AlgebraicSimplex.CoordinateRing L d where
  toFun := AlgebraicSimplex.coefficientMap e.toRingHom d
  invFun := AlgebraicSimplex.coefficientMap e.symm.toRingHom d
  left_inv x := by
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id L := by ext a; simp
    have h := DFunLike.congr_fun
      (AlgebraicSimplex.coefficientMap_comp e.toRingHom e.symm.toRingHom d) x
    rw [he, AlgebraicSimplex.coefficientMap_id] at h
    exact h
  right_inv x := by
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id L := by ext a; simp
    have h := DFunLike.congr_fun
      (AlgebraicSimplex.coefficientMap_comp e.symm.toRingHom e.toRingHom d) x
    rw [he, AlgebraicSimplex.coefficientMap_id] at h
    exact h
  map_mul' := (AlgebraicSimplex.coefficientMap e.toRingHom d).map_mul
  map_add' := (AlgebraicSimplex.coefficientMap e.toRingHom d).map_add

theorem coefficientEquiv_toRingHom (e : L ≃+* L) (d : ℕ) :
    (coefficientEquiv e d).toRingHom = AlgebraicSimplex.coefficientMap e.toRingHom d := rfl

/-- Coefficients move by e; torus monomials are fixed. -/
def laurentCoefficientEquiv (e : L ≃+* L) (d : ℕ) :
    MonoidAlgebra (CoordinateRing L d) (Multiplicative (ℤ × ℤ)) ≃+*
      MonoidAlgebra (CoordinateRing L d) (Multiplicative (ℤ × ℤ)) :=
  MonoidAlgebra.mapRingEquiv (Multiplicative (ℤ × ℤ)) (coefficientEquiv e d)

theorem laurentCoefficientEquiv_toRingHom (e : L ≃+* L) (d : ℕ) :
    (laurentCoefficientEquiv e d).toRingHom =
      MonoidAlgebra.mapRingHom (Multiplicative (ℤ × ℤ))
        (AlgebraicSimplex.coefficientMap e.toRingHom d) := rfl

@[simp] theorem laurentCoefficientEquiv_single (e : L ≃+* L) (d : ℕ) (m : (Multiplicative (ℤ × ℤ)))
    (a : AlgebraicSimplex.CoordinateRing L d) :
    laurentCoefficientEquiv e d (MonoidAlgebra.single m a) =
      MonoidAlgebra.single m (AlgebraicSimplex.coefficientMap e.toRingHom d a) :=
  MonoidAlgebra.mapRingEquiv_single _ _ _

theorem laurentCoefficientEquiv_algebraMap (e : L ≃+* L) (d : ℕ)
    (a : AlgebraicSimplex.CoordinateRing L d) :
    laurentCoefficientEquiv e d (algebraMap _ _ a) = algebraMap _ _ (coefficientEquiv e d a) :=
  DFunLike.congr_fun (MonoidAlgebra.mapRingHom_comp_algebraMap
    (M := (Multiplicative (ℤ × ℤ))) (coefficientEquiv e d).toRingHom) a

theorem laurentCoefficientEquiv_smul (e : L ≃+* L) (d : ℕ)
    (a : AlgebraicSimplex.CoordinateRing L d)
    (x : MonoidAlgebra (CoordinateRing L d) (Multiplicative (ℤ × ℤ))) :
    laurentCoefficientEquiv e d (a • x) =
      coefficientEquiv e d a • laurentCoefficientEquiv e d x := by
  ext m
  simp [laurentCoefficientEquiv, MonoidAlgebra.coeff_mapRingEquiv, smul_eq_mul]

end AlgebraicGeometry.AlgebraicSimplex
