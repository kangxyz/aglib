/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Auxiliary degree retractions and finite separable restriction kernels

A chosen primitive-element polynomial norm provides an existential integer-linear
map whose composite with restriction is multiplication by the actual extension
degree, in every Milnor degree and arbitrary characteristic. This auxiliary map
is not asserted to be canonical or compatible with extension towers.

Consequently restriction kernels are killed by the field degree. Restriction
detects torsion of coprime order, including prime-power torsion under prime-to-prime
degree extensions. Two restrictions of coprime finite separable degrees jointly
detect every original class. No injectivity on arbitrary classes is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial PolynomialNorm PolynomialResidue

variable (k E : Type*) [Field k] [Field E]

section Algebra

variable [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E]

/-- One primitive-element presentation supplies an auxiliary degree retraction
in every degree. No independence of this choice is claimed. -/
theorem exists_degree_retraction (n : ℕ) :
    ∃ T : K E n →ₗ[ℤ] K k n,
      ∀ x : K k n, T (map n (algebraMap k E) x) = (Module.finrank k E : ℤ) • x := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element k E
  let p : MonicIrreducible k :=
    ⟨minpoly k a, minpoly.monic (IsIntegral.of_finite k a),
      minpoly.irreducible (IsIntegral.of_finite k a)⟩
  let : Fact (Irreducible p.val) := ⟨p.property.2⟩
  let e : AdjoinRoot p.val ≃ₐ[k] E :=
    (IntermediateField.adjoinRootEquivAdjoin k (IsIntegral.of_finite k a)).trans
      ((IntermediateField.equivOfEq ha).trans IntermediateField.topEquiv)
  have hp : p.val.natDegree = Module.finrank k E :=
    (Field.primitive_element_iff_minpoly_natDegree_eq k a).mp ha
  refine ⟨(polynomialNorm n p).comp (map n e.symm.toRingHom), ?_⟩
  intro x
  have hc : e.symm.toRingHom.comp (algebraMap k E) =
      algebraMap k (AdjoinRoot p.val) := by
    ext c
    exact e.symm.commutes c
  rw [LinearMap.comp_apply, ← LinearMap.comp_apply (map n e.symm.toRingHom),
    ← map_comp, hc, polynomialNorm_map_constants, hp]

/-- Every element of a finite separable restriction kernel is killed by the
actual field degree, without any characteristic assumption. -/
theorem finrank_smul_eq_zero_of_map_eq_zero (n : ℕ) (x : K k n)
    (hx : map n (algebraMap k E) x = 0) : (Module.finrank k E : ℤ) • x = 0 := by
  obtain ⟨T, hT⟩ := exists_degree_retraction k E n
  rw [← hT x, hx, map_zero]

/-- Restricted torsion descends with the extra factor of the actual degree. -/
theorem mul_finrank_smul_eq_zero_of_smul_map_eq_zero (n : ℕ) (m : ℤ) (x : K k n)
    (hx : m • map n (algebraMap k E) x = 0) :
    (m * (Module.finrank k E : ℤ)) • x = 0 := by
  have h := finrank_smul_eq_zero_of_map_eq_zero k E n (m • x) (by rwa [map_smul])
  simpa only [smul_smul, mul_comm] using h

/-- A torsion class with order bound coprime to the extension degree is detected
by the actual restriction map. -/
theorem eq_zero_of_map_eq_zero_of_coprime (n m : ℕ)
    (hm : m.Coprime (Module.finrank k E)) (x : K k n)
    (hx : map n (algebraMap k E) x = 0) (hxm : (m : ℤ) • x = 0) : x = 0 := by
  obtain ⟨a, b, hab⟩ := hm.isCoprime
  have hd := finrank_smul_eq_zero_of_map_eq_zero k E n x hx
  calc
    x = (1 : ℤ) • x := (one_smul ℤ x).symm
    _ = (a * m + b * (Module.finrank k E : ℤ)) • x := by rw [hab]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, hxm, hd, smul_zero, smul_zero, add_zero]

/-- Finite separable prime-to-`p` degree restriction detects `p`-power torsion.
The arithmetic statement does not need to assume `p` is prime. -/
theorem eq_zero_of_map_eq_zero_of_coprime_pow (n p r : ℕ)
    (hp : p.Coprime (Module.finrank k E)) (x : K k n)
    (hx : map n (algebraMap k E) x = 0) (hxp : ((p ^ r : ℕ) : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_map_eq_zero_of_coprime k E n (p ^ r) (hp.pow_left r) x hx hxp

/-- Equality of two classes with coprime-order difference can be checked after
finite separable restriction. -/
theorem eq_of_map_eq_of_coprime (n m : ℕ)
    (hm : m.Coprime (Module.finrank k E)) (x y : K k n)
    (hxy : map n (algebraMap k E) x = map n (algebraMap k E) y)
    (hmxy : (m : ℤ) • (x - y) = 0) : x = y := by
  apply sub_eq_zero.mp
  exact eq_zero_of_map_eq_zero_of_coprime k E n m hm (x - y)
    (by rw [map_sub, hxy, sub_self]) hmxy

end Algebra

/-- The auxiliary retraction for an actual field map. All extension structures,
including the degree and separability hypotheses, are induced by that map. -/
theorem exists_degree_retraction_of_fieldMap (φ : k →+* E)
    (hfin : letI := φ.toAlgebra; FiniteDimensional k E)
    (hsep : letI := φ.toAlgebra; Algebra.IsSeparable k E) (n : ℕ) :
    let := φ.toAlgebra
    ∃ T : K E n →ₗ[ℤ] K k n,
      ∀ x : K k n, T (map n φ x) = (Module.finrank k E : ℤ) • x := by
  let := φ.toAlgebra
  let := hfin
  let := hsep
  exact exists_degree_retraction k E n

/-- Finite separable field-map restriction kernels are killed by the degree of
the map's own algebra structure. -/
theorem finrank_smul_eq_zero_of_fieldMap_eq_zero (φ : k →+* E)
    (hfin : letI := φ.toAlgebra; FiniteDimensional k E)
    (hsep : letI := φ.toAlgebra; Algebra.IsSeparable k E) (n : ℕ) (x : K k n)
    (hx : map n φ x = 0) :
    let := φ.toAlgebra
    (Module.finrank k E : ℤ) • x = 0 := by
  let := φ.toAlgebra
  let := hfin
  let := hsep
  exact finrank_smul_eq_zero_of_map_eq_zero k E n x hx

/-- Prime-to-order detection for an actual finite separable field map, with no
ambient algebra structure substituted for the map's own structure. -/
theorem eq_zero_of_fieldMap_eq_zero_of_coprime (φ : k →+* E)
    (hfin : letI := φ.toAlgebra; FiniteDimensional k E)
    (hsep : letI := φ.toAlgebra; Algebra.IsSeparable k E) (n m : ℕ)
    (hm : letI := φ.toAlgebra; m.Coprime (Module.finrank k E)) (x : K k n)
    (hx : map n φ x = 0) (hxm : (m : ℤ) • x = 0) : x = 0 := by
  let := φ.toAlgebra
  let := hfin
  let := hsep
  exact eq_zero_of_map_eq_zero_of_coprime k E n m hm x hx hxm

/-- Two finite separable restrictions of coprime degrees jointly detect the
original class. The two extensions need not be related by a tower. -/
theorem eq_zero_of_two_maps_eq_zero_of_coprime
    (L : Type*) [Field L] [Algebra k E] [Algebra k L]
    [FiniteDimensional k E] [FiniteDimensional k L]
    [Algebra.IsSeparable k E] [Algebra.IsSeparable k L]
    (hEL : (Module.finrank k E).Coprime (Module.finrank k L)) (n : ℕ) (x : K k n)
    (hE : map n (algebraMap k E) x = 0) (hL : map n (algebraMap k L) x = 0) : x = 0 :=
  eq_zero_of_map_eq_zero_of_coprime k L n (Module.finrank k E) hEL x hL
    (finrank_smul_eq_zero_of_map_eq_zero k E n x hE)

end MilnorK
