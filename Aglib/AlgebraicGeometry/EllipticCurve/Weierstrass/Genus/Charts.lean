/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.InfinityChart
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Cubic bases and overlap sections of the literal Weierstrass cubic

Besides its usual quadratic presentation over `R[x]`, the original affine
coordinate ring has a monic cubic presentation over `R[y]`. The infinity
ring already has the matching monic cubic presentation over `R[v]`.
On their original overlap the basis coordinates satisfy `x=u/v`, `y=1/v`.
The resulting overlap quotient has the single basis class `u²/v`. Its maps
are compared with the original homogeneous basic-open restrictions and
structural constants. The higher `Genus` leaf applies native Mayer–Vietoris
cohomology to these chart constructions. No nonzero discriminant is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial Module
open scoped Polynomial

namespace WeierstrassCurve.Projective

universe u
variable {R : Type u} [CommRing R]

/-- The original affine equation, monic in `x`, with coefficient variable `y`. -/
def affineCubicPolynomial (W : WeierstrassCurve R) : R[X][X] :=
  X ^ 3 + C (C W.a₂) * X ^ 2 + C (C W.a₄ - C W.a₁ * X) * X +
    C (C W.a₆ - C W.a₃ * X - X ^ 2)

lemma affineCubicPolynomial_monic (W : WeierstrassCurve R) :
    (affineCubicPolynomial W).Monic := by
  simpa only [affineCubicPolynomial, Cubic.toPoly, Polynomial.C_1, one_mul] using
    (Cubic.monic_of_a_eq_one (P :=
      ⟨1, C W.a₂, C W.a₄ - C W.a₁ * X, C W.a₆ - C W.a₃ * X - X ^ 2⟩) rfl)

/-- The original affine coordinate ring presented by a monic cubic in `x` over `R[y]`. -/
abbrev affineCubicRing (W : WeierstrassCurve R) := AdjoinRoot (affineCubicPolynomial W)

/-- The root of the monic cubic, representing the original affine coordinate `x`. -/
def affineCubicX (W : WeierstrassCurve R) : affineCubicRing W :=
  AdjoinRoot.root (affineCubicPolynomial W)

/-- The coefficient variable of the cubic presentation, representing the affine coordinate `y`. -/
def affineCubicY (W : WeierstrassCurve R) : affineCubicRing W :=
  AdjoinRoot.of (affineCubicPolynomial W) X

/-- The native coordinate relation in the monic cubic presentation. -/
lemma affineCubic_relation (W : WeierstrassCurve R) :
    affineCubicY W ^ 2 + algebraMap R _ W.a₁ * affineCubicX W * affineCubicY W +
      algebraMap R _ W.a₃ * affineCubicY W -
      (affineCubicX W ^ 3 + algebraMap R _ W.a₂ * affineCubicX W ^ 2 +
        algebraMap R _ W.a₄ * affineCubicX W + algebraMap R _ W.a₆) = 0 := by
  have h := AdjoinRoot.eval₂_root (affineCubicPolynomial W)
  conv_lhs at h => arg 3; unfold affineCubicPolynomial
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    map_sub, map_mul, map_pow] at h
  change affineCubicX W ^ 3 + algebraMap R _ W.a₂ * affineCubicX W ^ 2 +
    (algebraMap R _ W.a₄ - algebraMap R _ W.a₁ * affineCubicY W) * affineCubicX W +
    (algebraMap R _ W.a₆ - algebraMap R _ W.a₃ * affineCubicY W - affineCubicY W ^ 2) = 0 at h
  linear_combination -h

/-- The monic cubic presentation maps to the existing Mathlib coordinate ring. -/
def affineCubicToRing (W : WeierstrassCurve R) : affineCubicRing W →ₐ[R] affineRing W :=
  AdjoinRoot.liftAlgHom _ (Polynomial.aeval (affineY W)) (affineX W) (by
    simp only [affineCubicPolynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
      eval₂_C, eval₂_X, AlgHom.coe_toRingHom, map_sub, map_mul, map_pow,
      Polynomial.aeval_C, Polynomial.aeval_X]
    linear_combination -(affine_relation W))

/-- The inverse map is the original universal affine coordinate map. -/
def affineRingToCubic (W : WeierstrassCurve R) : affineRing W →ₐ[R] affineCubicRing W :=
  WeierstrassCurve.affineLift W (affineCubicX W) (affineCubicY W) (affineCubic_relation W)

@[simp] lemma affineCubicToRing_x (W : WeierstrassCurve R) :
    affineCubicToRing W (affineCubicX W) = affineX W := by
  simp [affineCubicToRing, affineCubicX]

@[simp] lemma affineCubicToRing_y (W : WeierstrassCurve R) :
    affineCubicToRing W (affineCubicY W) = affineY W := by
  simp [affineCubicToRing, affineCubicY, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_of]

@[simp] lemma affineRingToCubic_x (W : WeierstrassCurve R) :
    affineRingToCubic W (affineX W) = affineCubicX W := by
  simp [affineRingToCubic]

@[simp] lemma affineRingToCubic_y (W : WeierstrassCurve R) :
    affineRingToCubic W (affineY W) = affineCubicY W := by
  simp [affineRingToCubic]

/-- Actual coefficient-preserving isomorphism, with no replacement coordinate ring. -/
def affineCubicEquiv (W : WeierstrassCurve R) : affineCubicRing W ≃ₐ[R] affineRing W := by
  refine AlgEquiv.ofAlgHom (affineCubicToRing W) (affineRingToCubic W) ?_ ?_
  · apply WeierstrassCurve.affine_ext W <;> simp
  · apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change affineRingToCubic W (affineCubicToRing W (affineCubicY W)) = affineCubicY W
      simp
    · change affineRingToCubic W (affineCubicToRing W (affineCubicX W)) = affineCubicX W
      simp

variable [Nontrivial R]

lemma affineCubicPolynomial_natDegree (W : WeierstrassCurve R) :
    (affineCubicPolynomial W).natDegree = 3 := by
  simpa only [affineCubicPolynomial, Cubic.toPoly, Polynomial.C_1, one_mul] using
    (Cubic.natDegree_of_a_ne_zero (P :=
      ⟨1, C W.a₂, C W.a₄ - C W.a₁ * X, C W.a₆ - C W.a₃ * X - X ^ 2⟩) one_ne_zero)

lemma infinityPolynomial_natDegree (W : WeierstrassCurve R) :
    (infinityPolynomial W).natDegree = 3 := by
  have h := Cubic.natDegree_of_a_ne_zero (P :=
      ⟨1, C W.a₂ * X, C W.a₄ * X ^ 2 - C W.a₁ * X,
        C W.a₆ * X ^ 3 - C W.a₃ * X ^ 2 - X⟩) one_ne_zero
  rw [Cubic.toPoly, Polynomial.C_1, one_mul] at h
  exact h

/-- The affine chart has basis `1,x,x²` over the original polynomial ring in `y`. -/
def affineCubicBasis (W : WeierstrassCurve R) : Basis (Fin 3) R[X] (affineCubicRing W) :=
  (AdjoinRoot.powerBasis' (affineCubicPolynomial_monic W)).basis.reindex
    (finCongr (affineCubicPolynomial_natDegree W))

@[simp] lemma affineCubicBasis_apply (W : WeierstrassCurve R) (i : Fin 3) :
    affineCubicBasis W i = affineCubicX W ^ (i : ℕ) := by
  rw [affineCubicBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast]
  rfl

/-- The infinity chart has basis `1,u,u²` over the original polynomial ring in `v`. -/
def infinityCubicBasis (W : WeierstrassCurve R) : Basis (Fin 3) R[X] (infinityRing W) :=
  (AdjoinRoot.powerBasis' (infinityPolynomial_monic W)).basis.reindex
    (finCongr (infinityPolynomial_natDegree W))

@[simp] lemma infinityCubicBasis_apply (W : WeierstrassCurve R) (i : Fin 3) :
    infinityCubicBasis W i = infinityU W ^ (i : ℕ) := by
  rw [infinityCubicBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast]
  rfl

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open Polynomial
open scoped Polynomial LaurentPolynomial

universe u
variable {R : Type u} [CommRing R]

/-- The original affine restriction, composed with the proved cubic presentation. -/
def affineCubicToOverlap (W : WeierstrassCurve R) :
    affineCubicRing W →ₐ[R] infinityOverlapRing W where
  __ := (affineToInfinityOverlap W).comp (affineCubicEquiv W).toRingHom
  commutes' r := by
    change affineToInfinityOverlap W (affineCubicEquiv W (algebraMap R _ r)) = _
    rw [AlgEquiv.commutes, affineToInfinityOverlap_constant]

@[simp] lemma affineCubicToOverlap_x (W : WeierstrassCurve R) :
    affineCubicToOverlap W (affineCubicX W) =
      algebraMap (infinityRing W) (infinityOverlapRing W) (infinityU W) *
        IsLocalization.Away.invSelf (infinityV W) := by
  change affineToInfinityOverlap W (affineCubicToRing W (affineCubicX W)) = _
  rw [affineCubicToRing_x, affineToInfinityOverlap_x]

@[simp] lemma affineCubicToOverlap_y (W : WeierstrassCurve R) :
    affineCubicToOverlap W (affineCubicY W) =
      IsLocalization.Away.invSelf (infinityV W) := by
  change affineToInfinityOverlap W (affineCubicToRing W (affineCubicY W)) = _
  rw [affineCubicToRing_y, affineToInfinityOverlap_y]

variable [Nontrivial R]

/-- A basis over the original coefficient ring on the cubic affine chart. -/
def affineCubicMonomialBasis (W : WeierstrassCurve R) :
    Basis (Fin 3 × ℕ) R (affineCubicRing W) :=
  (Polynomial.basisMonomials R).smulTower' (affineCubicBasis W)

@[simp] lemma affineCubicMonomialBasis_apply (W : WeierstrassCurve R) (i : Fin 3) (n : ℕ) :
    affineCubicMonomialBasis W (i, n) = affineCubicY W ^ n * affineCubicX W ^ (i : ℕ) := by
  simp only [affineCubicMonomialBasis, Module.Basis.smulTower'_apply,
    Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow,
    affineCubicBasis_apply, Algebra.smul_def, map_pow]
  rfl

/-- A basis over the original coefficient ring on the infinity chart. -/
def infinityMonomialBasis (W : WeierstrassCurve R) :
    Basis (Fin 3 × ℕ) R (infinityRing W) :=
  (Polynomial.basisMonomials R).smulTower' (infinityCubicBasis W)

@[simp] lemma infinityMonomialBasis_apply (W : WeierstrassCurve R) (i : Fin 3) (n : ℕ) :
    infinityMonomialBasis W (i, n) = infinityV W ^ n * infinityU W ^ (i : ℕ) := by
  simp only [infinityMonomialBasis, Module.Basis.smulTower'_apply,
    Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow,
    infinityCubicBasis_apply, Algebra.smul_def, map_pow]
  rfl

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open Polynomial
open scoped Polynomial LaurentPolynomial

universe u
variable {R : Type u} [CommRing R]

instance infinityOverlapPolynomialLocalization (W : WeierstrassCurve R) :
    IsLocalization (Algebra.algebraMapSubmonoid (infinityRing W)
      (Submonoid.powers (X : R[X]))) (infinityOverlapRing W) := by
  change IsLocalization ((Submonoid.powers (X : R[X])).map
    (algebraMap R[X] (infinityRing W)).toMonoidHom) (infinityOverlapRing W)
  rw [Submonoid.map_powers]
  change IsLocalization.Away (infinityV W) (infinityOverlapRing W)
  infer_instance

instance infinityOverlapLaurentAlgebra (W : WeierstrassCurve R) :
    Algebra R[T;T⁻¹] (infinityOverlapRing W) :=
  localizationAlgebra (Submonoid.powers (X : R[X])) (infinityRing W)

instance infinityOverlapLaurentPolynomialTower (W : WeierstrassCurve R) :
    IsScalarTower R[X] R[T;T⁻¹] (infinityOverlapRing W) :=
  isScalarTower_localizationAlgebra
    (Submonoid.powers (X : R[X])) (infinityRing W)

instance infinityOverlapLaurentTower (W : WeierstrassCurve R) :
    IsScalarTower R R[T;T⁻¹] (infinityOverlapRing W) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  change algebraMap R (infinityOverlapRing W) r =
    algebraMap R[T;T⁻¹] (infinityOverlapRing W) (LaurentPolynomial.C r)
  rw [← Polynomial.toLaurent_C]
  change _ = algebraMap R[T;T⁻¹] (infinityOverlapRing W)
    (algebraMap R[X] R[T;T⁻¹] (Polynomial.C r))
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R R[X] (infinityOverlapRing W)]
  rfl

variable [Nontrivial R]

/-- The original infinity-overlap localization has the same monic basis over
the original Laurent coefficient ring. -/
def infinityOverlapBasis (W : WeierstrassCurve R) :
    Basis (Fin 3) R[T;T⁻¹] (infinityOverlapRing W) :=
  (infinityCubicBasis W).localizationLocalization R[T;T⁻¹]
    (Submonoid.powers (X : R[X])) (infinityOverlapRing W)

@[simp] lemma infinityOverlapBasis_apply (W : WeierstrassCurve R) (i : Fin 3) :
    infinityOverlapBasis W i =
      algebraMap (infinityRing W) (infinityOverlapRing W) (infinityU W) ^ (i : ℕ) := by
  rw [infinityOverlapBasis, Module.Basis.localizationLocalization_apply,
    infinityCubicBasis_apply, map_pow]

@[simp] lemma infinityOverlapBasis_repr_map (W : WeierstrassCurve R)
    (a : infinityRing W) (i : Fin 3) :
    (infinityOverlapBasis W).repr
      (algebraMap (infinityRing W) (infinityOverlapRing W) a) i =
        Polynomial.toLaurent ((infinityCubicBasis W).repr a i) := by
  exact Module.Basis.localizationLocalization_repr_algebraMap R[T;T⁻¹]
    (Submonoid.powers (X : R[X])) (infinityOverlapRing W) (infinityCubicBasis W) a i

omit [Nontrivial R] in
lemma infinityOverlapLaurent_T_one (W : WeierstrassCurve R) :
    algebraMap R[T;T⁻¹] (infinityOverlapRing W) (LaurentPolynomial.T 1) =
      algebraMap (infinityRing W) (infinityOverlapRing W) (infinityV W) := by
  rw [← Polynomial.toLaurent_X]
  change algebraMap R[T;T⁻¹] (infinityOverlapRing W)
    (algebraMap R[X] R[T;T⁻¹] X) = _
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R[X] (infinityRing W) (infinityOverlapRing W)]
  rfl

omit [Nontrivial R] in
lemma infinityOverlapLaurent_T_neg_one (W : WeierstrassCurve R) :
    algebraMap R[T;T⁻¹] (infinityOverlapRing W) (LaurentPolynomial.T (-1)) =
      IsLocalization.Away.invSelf (infinityV W) := by
  apply (IsLocalization.Away.algebraMap_isUnit (infinityV W)).mul_right_inj.mp
  rw [IsLocalization.Away.mul_invSelf, ← infinityOverlapLaurent_T_one,
    ← map_mul, ← LaurentPolynomial.T_add]
  norm_num [LaurentPolynomial.T_zero]

/-- Coefficient of `u²/v` in the actual overlap ring. -/
def infinityOverlapResidue (W : WeierstrassCurve R) : infinityOverlapRing W →ₗ[R] R where
  toFun a := ((infinityOverlapBasis W).repr a 2).coeff (-1)
  map_add' a b := by simp
  map_smul' r a := by
    change (((infinityOverlapBasis W).repr.restrictScalars R) (r • a) 2).coeff (-1) = _
    rw [LinearEquiv.map_smul]
    rfl

omit [Nontrivial R] in
private lemma toLaurent_coeff_neg (p : R[X]) (n : ℤ) (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_zero]
  | monomial m r =>
    rw [Polynomial.toLaurent_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T]
    exact Finsupp.single_eq_of_ne (by omega)

/-- The residue annihilates the original infinity-chart restriction map. -/
lemma infinityOverlapResidue_map (W : WeierstrassCurve R) (a : infinityRing W) :
    infinityOverlapResidue W
      (algebraMap (infinityRing W) (infinityOverlapRing W) a) = 0 := by
  change ((infinityOverlapBasis W).repr
    (algebraMap (infinityRing W) (infinityOverlapRing W) a) 2).coeff (-1) = 0
  rw [infinityOverlapBasis_repr_map]
  exact toLaurent_coeff_neg _ _ (by omega)

/-- The actual overlap element that represents the unique possible H¹ class. -/
def infinityOverlapGenusClass (W : WeierstrassCurve R) : infinityOverlapRing W :=
  (LaurentPolynomial.T (-1) : R[T;T⁻¹]) • infinityOverlapBasis W 2

@[simp] lemma infinityOverlapResidue_genusClass (W : WeierstrassCurve R) :
    infinityOverlapResidue W (infinityOverlapGenusClass W) = 1 := by
  change (((infinityOverlapBasis W).repr
    ((LaurentPolynomial.T (-1) : R[T;T⁻¹]) • infinityOverlapBasis W 2)) 2).coeff (-1) = 1
  rw [map_smul, Module.Basis.repr_self]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
    LaurentPolynomial.T_apply, ite_true]

/-- The original overlap is free on its three Laurent-coordinate monomial families. -/
def infinityOverlapMonomialBasis (W : WeierstrassCurve R) :
    Basis (Fin 3 × ℤ) R (infinityOverlapRing W) :=
  (AddMonoidAlgebra.basis ℤ R).smulTower' (infinityOverlapBasis W)

@[simp] lemma infinityOverlapMonomialBasis_apply
    (W : WeierstrassCurve R) (i : Fin 3) (n : ℤ) :
    infinityOverlapMonomialBasis W (i, n) =
      (LaurentPolynomial.T n : R[T;T⁻¹]) • infinityOverlapBasis W i := by
  rw [infinityOverlapMonomialBasis, Module.Basis.smulTower'_apply]
  rfl

lemma infinityOverlapMonomialBasis_coord (W : WeierstrassCurve R)
    (a : infinityOverlapRing W) :
    (infinityOverlapMonomialBasis W).coord (2, -1) a = infinityOverlapResidue W a := by
  rw [Module.Basis.coord_apply, infinityOverlapMonomialBasis, Module.Basis.smulTower'_repr]
  rfl

/-- The infinity restriction sends its actual basis to the nonnegative monomials. -/
lemma infinityMonomialBasis_map (W : WeierstrassCurve R) (i : Fin 3) (n : ℕ) :
    algebraMap (infinityRing W) (infinityOverlapRing W) (infinityMonomialBasis W (i, n)) =
      infinityOverlapMonomialBasis W (i, n) := by
  rw [infinityMonomialBasis_apply, map_mul, map_pow, map_pow,
    infinityOverlapMonomialBasis_apply, infinityOverlapBasis_apply, Algebra.smul_def]
  congr 1
  rw [← infinityOverlapLaurent_T_one, ← map_pow, LaurentPolynomial.T_pow, mul_one]

/-- The affine restriction sends `yⁿxⁱ` to the actual monomial `uⁱv^(-i-n)`. -/
lemma affineCubicMonomialBasis_map (W : WeierstrassCurve R) (i : Fin 3) (n : ℕ) :
    affineCubicToOverlap W (affineCubicMonomialBasis W (i, n)) =
      infinityOverlapMonomialBasis W (i, -(i : ℤ) - n) := by
  rw [affineCubicMonomialBasis_apply, map_mul, map_pow, map_pow,
    affineCubicToOverlap_x, affineCubicToOverlap_y,
    infinityOverlapMonomialBasis_apply, infinityOverlapBasis_apply, Algebra.smul_def]
  rw [show -(i : ℤ) - n = ((n + (i : ℕ) : ℕ) : ℤ) * (-1) by push_cast; ring,
    ← LaurentPolynomial.T_pow, map_pow, infinityOverlapLaurent_T_neg_one]
  ring

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open Polynomial
open scoped Polynomial LaurentPolynomial

universe u
variable {R : Type u} [CommRing R] [Nontrivial R]

/-- The existing affine overlap map with its unchanged coefficient action. -/
def affineToInfinityOverlapAlgHom (W : WeierstrassCurve R) :
    affineRing W →ₐ[R] infinityOverlapRing W where
  __ := affineToInfinityOverlap W
  commutes' := affineToInfinityOverlap_constant W

/-- Sum of the images of the two original chart restriction maps. -/
def overlapChartSubmodule (W : WeierstrassCurve R) :
    Submodule R (infinityOverlapRing W) :=
  LinearMap.range (affineToInfinityOverlapAlgHom W).toLinearMap ⊔
    LinearMap.range (IsScalarTower.toAlgHom R (infinityRing W) (infinityOverlapRing W)).toLinearMap

omit [Nontrivial R] in
private lemma range_eq_span_basis {M N ι : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (b : Basis ι R M) (f : M →ₗ[R] N) :
    LinearMap.range f = Submodule.span R (Set.range (fun i => f (b i))) := by
  calc
    LinearMap.range f = (⊤ : Submodule R M).map f := (Submodule.map_top f).symm
    _ = (Submodule.span R (Set.range b)).map f := by rw [b.span_eq]
    _ = Submodule.span R (f '' Set.range b) := Submodule.map_span f _
    _ = Submodule.span R (Set.range (fun i => f (b i))) := by
      rw [← Set.range_comp]
      rfl

omit [Nontrivial R] in
lemma affineCubicToOverlap_range (W : WeierstrassCurve R) :
    LinearMap.range (affineCubicToOverlap W).toLinearMap =
      LinearMap.range (affineToInfinityOverlapAlgHom W).toLinearMap := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨affineCubicEquiv W a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(affineCubicEquiv W).symm a, ?_⟩
    change affineToInfinityOverlap W
      (affineCubicEquiv W ((affineCubicEquiv W).symm a)) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl

private lemma chartMonomialIndices :
    Set.range (fun q : Fin 3 × ℕ => (q.1, -(q.1 : ℤ) - q.2)) ∪
      Set.range (fun q : Fin 3 × ℕ => (q.1, (q.2 : ℤ))) =
        {q : Fin 3 × ℤ | q ≠ (2, -1)} := by
  ext ⟨i, n⟩
  constructor
  · intro h he
    rcases h with ⟨⟨j, m⟩, hq⟩ | ⟨⟨j, m⟩, hq⟩
    · have hi := congrArg Prod.fst (hq.trans he)
      have hm := congrArg Prod.snd (hq.trans he)
      dsimp at hi hm
      rw [hi] at hm
      norm_num at hm
      omega
    · have hm := congrArg Prod.snd (hq.trans he)
      dsimp at hm
      omega
  · intro h
    by_cases hn : 0 ≤ n
    · right
      refine ⟨(i, n.toNat), ?_⟩
      apply Prod.ext
      · rfl
      · dsimp
        omega
    · left
      have hi : n ≤ -(i : ℤ) := by
        fin_cases i <;> simp at h ⊢ <;> omega
      refine ⟨(i, (-n - (i : ℤ)).toNat), ?_⟩
      apply Prod.ext
      · rfl
      · dsimp
        omega

/-- Every overlap basis vector except `u²/v` belongs to one original chart image. -/
theorem overlapChartSubmodule_eq_span (W : WeierstrassCurve R) :
    overlapChartSubmodule W = Submodule.span R
      (infinityOverlapMonomialBasis W '' {q : Fin 3 × ℤ | q ≠ (2, -1)}) := by
  rw [overlapChartSubmodule, ← affineCubicToOverlap_range,
    range_eq_span_basis (affineCubicMonomialBasis W),
    range_eq_span_basis (infinityMonomialBasis W)]
  have ha : (fun q : Fin 3 × ℕ =>
      (affineCubicToOverlap W).toLinearMap (affineCubicMonomialBasis W q)) =
      infinityOverlapMonomialBasis W ∘ (fun q : Fin 3 × ℕ => (q.1, -(q.1 : ℤ) - q.2)) := by
    funext ⟨i, n⟩
    exact affineCubicMonomialBasis_map W i n
  have hb : (fun q : Fin 3 × ℕ =>
      (IsScalarTower.toAlgHom R (infinityRing W) (infinityOverlapRing W)).toLinearMap
        (infinityMonomialBasis W q)) =
      infinityOverlapMonomialBasis W ∘ (fun q : Fin 3 × ℕ => (q.1, (q.2 : ℤ))) := by
    funext ⟨i, n⟩
    exact infinityMonomialBasis_map W i n
  rw [ha, hb, ← Submodule.span_union, Set.range_comp, Set.range_comp,
    ← Set.image_union, chartMonomialIndices]

/-- The chart-image sum is exactly the kernel of the original coefficient of `u²/v`. -/
theorem overlapChartSubmodule_eq_ker (W : WeierstrassCurve R) :
    overlapChartSubmodule W =
      LinearMap.ker ((infinityOverlapMonomialBasis W).coord (2, -1)) := by
  rw [overlapChartSubmodule_eq_span]
  ext a
  rw [Module.Basis.mem_span_image, LinearMap.mem_ker, Module.Basis.coord_apply]
  constructor
  · intro h
    by_contra hn
    exact h (Finsupp.mem_support_iff.mpr hn) rfl
  · intro h q hq he
    subst q
    exact (Finsupp.mem_support_iff.mp hq) h

/-- The quotient of the actual overlap ring by its two original chart images is
the original coefficient ring, via the single surviving monomial coordinate. -/
def overlapChartQuotientEquiv (W : WeierstrassCurve R) :
    (infinityOverlapRing W ⧸ overlapChartSubmodule W) ≃ₗ[R] R :=
  (Submodule.quotEquivOfEq _ _ (overlapChartSubmodule_eq_ker W)).trans
    (((infinityOverlapMonomialBasis W).coord (2, -1)).quotKerEquivOfSurjective (by
      intro r
      exact ⟨r • infinityOverlapMonomialBasis W (2, -1), by
        rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_same, smul_eq_mul, mul_one]⟩))

/-- The quotient equivalence is the original Laurent coefficient, not a chosen
isomorphism between abstract one-dimensional modules. -/
lemma overlapChartQuotientEquiv_apply (W : WeierstrassCurve R)
    (a : infinityOverlapRing W) :
    overlapChartQuotientEquiv W (Submodule.Quotient.mk a) = infinityOverlapResidue W a := by
  simp only [overlapChartQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, infinityOverlapMonomialBasis_coord]

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u
variable {R : Type u} [CommRing R]

/-- The native homogeneous localization for the actual two-chart intersection. -/
abbrev homogeneousOverlapRing (W : WeierstrassCurve R) :=
  HomogeneousLocalization.Away (grading W) (coordinate W 1 * coordinate W 2)

/-- The original homogeneous restriction from the infinity chart to the two-chart overlap. -/
def infinityChartToHomogeneousOverlap (W : WeierstrassCurve R) :
    chartRing W 1 →+* homogeneousOverlapRing W :=
  HomogeneousLocalization.awayMap (grading W) (coordinate_mem W 2) rfl

/-- The original homogeneous restriction from the affine chart to the two-chart overlap. -/
def affineChartToHomogeneousOverlap (W : WeierstrassCurve R) :
    chartRing W 2 →+* homogeneousOverlapRing W :=
  HomogeneousLocalization.awayMap (grading W) (coordinate_mem W 1) (mul_comm _ _)

instance homogeneousOverlapChartAlgebra (W : WeierstrassCurve R) :
    Algebra (chartRing W 1) (homogeneousOverlapRing W) :=
  (infinityChartToHomogeneousOverlap W).toAlgebra

instance homogeneousOverlapChartLocalization (W : WeierstrassCurve R) :
    IsLocalization.Away (normalizedCoordinate W 1 2) (homogeneousOverlapRing W) := by
  simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one,
    normalizedCoordinate] using
    HomogeneousLocalization.Away.isLocalization_mul (coordinate_mem W 1)
      (coordinate_mem W 2) rfl (by decide)

/-- The overlap ring used by the monic bases is the original homogeneous overlap localization. -/
def homogeneousOverlapEquiv (W : WeierstrassCurve R) :
    homogeneousOverlapRing W ≃+* infinityOverlapRing W :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (normalizedCoordinate W 1 2))
    (T := Submonoid.powers (infinityV W))
    (homogeneousOverlapRing W) (infinityOverlapRing W) (infinityChartRingEquiv W).symm (by
    rw [Submonoid.map_powers]
    congr 1
    change fromInfinityProjectiveChart W (normalizedCoordinate W 1 2) = infinityV W
    simp)

@[simp] lemma homogeneousOverlapEquiv_infinity (W : WeierstrassCurve R)
    (a : chartRing W 1) :
    homogeneousOverlapEquiv W (infinityChartToHomogeneousOverlap W a) =
      algebraMap (infinityRing W) (infinityOverlapRing W) (fromInfinityProjectiveChart W a) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (S := homogeneousOverlapRing W) (Q := infinityOverlapRing W) _ a

/-- Multiplying an affine coordinate by `v=Z/Y` gives the original infinity coordinate. -/
lemma homogeneousOverlap_coordinate_mul_v (W : WeierstrassCurve R) (i : Fin 3) :
    affineChartToHomogeneousOverlap W (normalizedCoordinate W 2 i) *
      infinityChartToHomogeneousOverlap W (normalizedCoordinate W 1 2) =
        infinityChartToHomogeneousOverlap W (normalizedCoordinate W 1 i) := by
  apply HomogeneousLocalization.val_injective
  simp only [affineChartToHomogeneousOverlap, infinityChartToHomogeneousOverlap,
    normalizedCoordinate, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul]
  ring

lemma homogeneousOverlapEquiv_affine_constant (W : WeierstrassCurve R) (r : R) :
    homogeneousOverlapEquiv W (affineChartToHomogeneousOverlap W (chartConstant W 2 r)) =
      algebraMap R (infinityOverlapRing W) r := by
  have h : affineChartToHomogeneousOverlap W (chartConstant W 2 r) =
      infinityChartToHomogeneousOverlap W (chartConstant W 1 r) := by
    simp only [affineChartToHomogeneousOverlap, infinityChartToHomogeneousOverlap,
      chartConstant, RingHom.comp_apply, HomogeneousLocalization.awayMap_fromZeroRingHom]
  rw [h, homogeneousOverlapEquiv_infinity, fromInfinityProjectiveChart_constant,
    ← IsScalarTower.algebraMap_apply]

lemma homogeneousOverlapEquiv_affine_coordinate (W : WeierstrassCurve R) (i : Fin 3) :
    homogeneousOverlapEquiv W
      (affineChartToHomogeneousOverlap W (normalizedCoordinate W 2 i)) =
        algebraMap (infinityRing W) (infinityOverlapRing W)
          (![infinityU W, 1, infinityV W] i) * IsLocalization.Away.invSelf (infinityV W) := by
  apply (IsLocalization.Away.algebraMap_isUnit (infinityV W)).mul_left_inj.mp
  have h := congrArg (homogeneousOverlapEquiv W) (homogeneousOverlap_coordinate_mul_v W i)
  simp only [map_mul, homogeneousOverlapEquiv_infinity,
    fromInfinityProjectiveChart_normalizedCoordinate, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons] at h
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (infinityV W)),
    IsLocalization.Away.mul_invSelf, mul_one]
  exact h

/-- The canonical restriction from the affine projective chart is precisely the
already constructed map `x=u/v`, `y=1/v`, including the coefficient map. -/
theorem homogeneousOverlapEquiv_affineMap (W : WeierstrassCurve R) :
    (homogeneousOverlapEquiv W).toRingHom.comp
      ((affineChartToHomogeneousOverlap W).comp (toProjectiveChart W)) =
        affineToInfinityOverlap W := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change homogeneousOverlapEquiv W
        (affineChartToHomogeneousOverlap W
          (toProjectiveChart W (algebraMap R (affineRing W) r))) =
            affineToInfinityOverlap W (algebraMap R (affineRing W) r)
      rw [toProjectiveChart_constant, homogeneousOverlapEquiv_affine_constant,
        affineToInfinityOverlap_constant]
    · change homogeneousOverlapEquiv W
        (affineChartToHomogeneousOverlap W (toProjectiveChart W (affineX W))) =
          affineToInfinityOverlap W (affineX W)
      rw [toProjectiveChart_affineX, homogeneousOverlapEquiv_affine_coordinate,
        affineToInfinityOverlap_x]
      rfl
  · change homogeneousOverlapEquiv W
      (affineChartToHomogeneousOverlap W (toProjectiveChart W (affineY W))) =
        affineToInfinityOverlap W (affineY W)
    rw [toProjectiveChart_affineY, homogeneousOverlapEquiv_affine_coordinate,
      affineToInfinityOverlap_y]
    simp

end WeierstrassCurve.Projective

namespace WeierstrassCurve.Projective

open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {k : Type u} [Field k]

/-- The original structural morphism on a positive homogeneous basic open. -/
lemma basicOpen_structureMap (W : WeierstrassCurve k)
    (f : homogeneousCoordinateRing W) {m : ℕ} (hf : f ∈ grading W m) (hm : 0 < m) :
    (Proj.basicOpen (grading W) f).ι ≫ structureMap W =
      (Proj.basicOpenIsoSpec (grading W) f hf hm).hom ≫
        Spec.map (CommRingCat.ofHom
          ((HomogeneousLocalization.fromZeroRingHom (grading W)
            (Submonoid.powers f)).comp (constToGradeZero W))) := by
  apply (cancel_epi (Proj.basicOpenIsoSpec (grading W) f hf hm).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Proj.basicOpenIsoSpec_inv_ι, structureMap, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- Canonical structural constants become the original homogeneous constant
fractions under the actual basic-open section isomorphism. -/
lemma basicOpen_constantSection (W : WeierstrassCurve k)
    (f : homogeneousCoordinateRing W) {m : ℕ} (hf : f ∈ grading W m)
    (hm : 0 < m) (r : k) :
    Scheme.constantSection (curveOver W) (Proj.basicOpen (grading W) f) r =
      (Proj.awayToSection (grading W) f).hom
        (HomogeneousLocalization.fromZeroRingHom (grading W)
          (Submonoid.powers f) (constToGradeZero W r)) := by
  let U := Proj.basicOpen (grading W) f
  let c := (HomogeneousLocalization.fromZeroRingHom (grading W)
    (Submonoid.powers f)).comp (constToGradeZero W)
  have hb : (Proj.basicOpenToSpec (grading W) f).appTop =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (grading W) f ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top (grading W) f
  have he : (Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ structureMap W).appTop =
      CommRingCat.ofHom c ≫ Proj.awayToSection (grading W) f ≫ U.topIso.inv := by
    rw [basicOpen_structureMap W f hf hm, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Proj.basicOpenIsoSpec_hom, hb]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  have ht : U.ι.appTop ≫ U.topIso.hom =
      (scheme W).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl
  have h := congrArg (fun t => t ≫ U.topIso.hom) he
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  rw [ht] at h
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) r

end WeierstrassCurve.Projective
