/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Aglib.AlgebraicGeometry.Group.RootsHopfAlgebra
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The actual cyclotomic primitive-root cover

New bounded construction for K2-018#prop:k2018-arithmetic-characters,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982, engineering HEAD 0ab5eec.
The algebra is literally R[T]/Phi_n(T). Finite freeness, positive rank,
faithful flatness, and etaleness are constructed rather than assumed.
The primitive root in every field-valued fibre is the image of this same T.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
open Polynomial AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Group.PrimitiveRootCover

universe u
variable (R : Type u) [CommRing R] (n : ℕ) [NeZero n]

/-- The actual primitive-root-adjoining algebra, not the entire roots algebra. -/
abbrev Cover := AdjoinRoot (cyclotomic n R)
abbrev root : Cover R n := AdjoinRoot.root (cyclotomic n R)

instance finite : Module.Finite R (Cover R n) :=
  (cyclotomic.monic n R).finite_adjoinRoot

instance free : Module.Free R (Cover R n) :=
  (cyclotomic.monic n R).free_adjoinRoot

omit [NeZero n] in
theorem root_cyclotomic : aeval (root R n) (cyclotomic n R) = 0 := by
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

omit [NeZero n] in
/-- The same quotient root is an nth root of unity, by the actual cyclotomic
factorization of X^n-1. -/
theorem root_pow : root R n ^ n = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one n R
  have h := congrArg (aeval (root R n)) hg
  simpa [root_cyclotomic, sub_eq_zero] using h

theorem root_isUnit : IsUnit (root R n) := by
  refine isUnit_iff_exists_inv.mpr ⟨root R n ^ (n - 1), ?_⟩
  rw [← pow_succ']
  simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))] using root_pow R n

/-- Evaluating the differentiated factorization makes the cyclotomic
derivative a factor of n T^(n-1), an actual unit on this quotient. -/
theorem derivative_isUnit (hunit : IsUnit (n : R)) :
    IsUnit (aeval (root R n) (cyclotomic n R).derivative) := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one n R
  have hd := congrArg (aeval (root R n)) (congrArg derivative hg)
  have hfactor : (n : Cover R n) * root R n ^ (n - 1) =
      aeval (root R n) (cyclotomic n R).derivative * aeval (root R n) g := by
    simpa [derivative_mul, derivative_sub, derivative_X_pow, root_cyclotomic] using hd
  have hn : IsUnit (n : Cover R n) := by
    simpa using hunit.map (algebraMap R (Cover R n))
  have hu := hn.mul ((root_isUnit R n).pow (n - 1))
  rw [hfactor] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- No etale premise is retained: the derivative-unit presentation proves it. -/
theorem etale (hunit : IsUnit (n : R)) : Algebra.Etale R (Cover R n) := by
  let q := cyclotomic n R
  let P : StandardEtalePair R := ⟨q, cyclotomic.monic n R, q.derivative, 1, 0, 1, by simp⟩
  let L := Localization.Away (AdjoinRoot.mk q q.derivative)
  have hmk : IsUnit (AdjoinRoot.mk q q.derivative) := by
    simpa [AdjoinRoot.aeval_eq] using derivative_isUnit R n hunit
  let e : P.Ring ≃ₐ[R] Cover R n := P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot q) L _ hmk).symm.restrictScalars R)
  exact Algebra.Etale.of_equiv e

omit [NeZero n] in
/-- Invertibility persists on the actual cover, as needed by its roots Hopf
coefficient algebra. -/
theorem level_isUnit (hunit : IsUnit (n : R)) : IsUnit (n : Cover R n) := by
  simpa using hunit.map (algebraMap R (Cover R n))

/-- The accepted actual roots Hopf algebra is finite etale on the new cover. -/
theorem rootedCoefficient_etale (hunit : IsUnit (n : R)) :
    Algebra.Etale (Cover R n) (RootsHopfAlgebra.H (Cover R n) n) :=
  RootsHopfAlgebra.etale (Cover R n) n (level_isUnit R n hunit)

section NontrivialBase
variable [Nontrivial R]

omit [NeZero n] in
theorem rank_eq_totient : Module.finrank R (Cover R n) = n.totient := by
  rw [(AdjoinRoot.powerBasis' (cyclotomic.monic n R)).finrank]
  exact natDegree_cyclotomic n R

theorem rank_pos : 0 < Module.finrank R (Cover R n) := by
  rw [rank_eq_totient]
  exact Nat.totient_pos.mpr (NeZero.pos n)

theorem algebraMap_injective : Function.Injective (algebraMap R (Cover R n)) :=
  AdjoinRoot.of.injective_of_monic_of_degree_pos (cyclotomic.monic n R)
    (degree_cyclotomic_pos n R (NeZero.pos n))

instance nontrivial : Nontrivial (Cover R n) :=
  Function.Injective.nontrivial (algebraMap_injective R n)

instance faithfullyFlat : Module.FaithfullyFlat R (Cover R n) := inferInstance

/-- The actual affine cover morphism, with its original base structure map. -/
def coverMap : Spec (.of (Cover R n)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Cover R n)))

instance coverMap_finite : IsFinite (coverMap R n) := by
  rw [coverMap, IsFinite.SpecMap_iff]
  change (algebraMap R (Cover R n)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

omit [Nontrivial R] in
theorem coverMap_etale (hunit : IsUnit (n : R)) : Etale (coverMap R n) := by
  let := etale R n hunit
  rw [coverMap, HasRingHomProperty.Spec_iff (P := @Etale)]
  change (algebraMap R (Cover R n)).Etale
  rw [RingHom.etale_algebraMap]
  infer_instance

/-- Faithful flatness is displayed on the actual scheme map as flatness and
surjectivity, so this really is a cover. -/
theorem coverMap_flat_surjective : Flat (coverMap R n) ∧ Surjective (coverMap R n) := by
  rw [coverMap, flat_and_surjective_SpecMap_iff]
  change (algebraMap R (Cover R n)).FaithfullyFlat
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

end NontrivialBase

section FieldPoints
variable (F : Type u) [Field F] [Algebra R F]

/-- The root in a field-valued fibre is the image of the actual quotient root. -/
def fieldRoot (f : Cover R n →ₐ[R] F) : rootsOfUnity n F :=
  rootsOfUnity.mkOfPowEq (f (root R n)) (by rw [← map_pow, root_pow, map_one])

@[simp] theorem fieldRoot_value (f : Cover R n →ₐ[R] F) :
    ((fieldRoot R n F f : Fˣ) : F) = f (root R n) :=
  rootsOfUnity.coe_mkOfPowEq _

/-- Primitivity is derived from the cyclotomic relation in this field fibre.
The unit hypothesis supplies the nonzero characteristic condition; no
characteristic-zero or perfection hypothesis is needed. -/
theorem fieldRoot_primitive (hunit : IsUnit (n : R)) (f : Cover R n →ₐ[R] F) :
    IsPrimitiveRoot ((fieldRoot R n F f : Fˣ) : F) n := by
  have hn : IsUnit (n : F) := by simpa using hunit.map (algebraMap R F)
  let : NeZero (n : F) := ⟨hn.ne_zero⟩
  rw [fieldRoot_value]
  apply isRoot_cyclotomic_iff.mp
  have hc := congrArg f (root_cyclotomic R n)
  rw [← aeval_algHom_apply] at hc
  simpa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, IsRoot.def] using hc


end FieldPoints

section GenericFibre
variable (K : Type u) [Field K] [Algebra R K]

/-- This is the original generic fibre of the actual cover, retaining its
literal scalar-extension map. It need not be a field. -/
abbrev GenericFibre := K ⊗[R] Cover R n
abbrev genericRoot : GenericFibre R n K := (1 : K) ⊗ₜ[R] root R n

omit [NeZero n] in
theorem genericRoot_pow : genericRoot R n K ^ n = 1 := by
  simp [genericRoot, Algebra.TensorProduct.tmul_pow, root_pow, Algebra.TensorProduct.one_def]

variable (F : Type u) [Field F] [Algebra K F] [Algebra R F] [IsScalarTower R K F]

/-- Restriction of a point on the SAME generic fibre to the original cover. -/
def genericPointRestriction (f : GenericFibre R n K →ₐ[K] F) : Cover R n →ₐ[R] F :=
  (Algebra.TensorProduct.liftEquivRight R K (Cover R n) F).symm f

omit [NeZero n] in
@[simp] theorem genericPointRestriction_root (f : GenericFibre R n K →ₐ[K] F) :
    genericPointRestriction R n K F f (root R n) = f (genericRoot R n K) := rfl

/-- Every field-valued point of the original generic fibre has the required
primitive root, derived from its actual quotient relation. -/
theorem genericRoot_primitive (hunit : IsUnit (n : R))
    (f : GenericFibre R n K →ₐ[K] F) : IsPrimitiveRoot (f (genericRoot R n K)) n := by
  simpa using fieldRoot_primitive R n F hunit (genericPointRestriction R n K F f)

end GenericFibre

section GeometricPoint
variable (K : Type u) [Field K] [Algebra R K]

/-- Every original generic fibre has an actual geometric point. A root of
the nonconstant cyclotomic polynomial is constructed in the closure; no
primitive root, point, or field-factor decomposition is supplied as input. -/
theorem exists_geometricPoint :
    Nonempty (GenericFibre R n K →ₐ[K] AlgebraicClosure K) := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (cyclotomic n (AlgebraicClosure K))
    (ne_of_gt (degree_cyclotomic_pos n (AlgebraicClosure K) (NeZero.pos n)))
  let f : Cover R n →ₐ[R] AlgebraicClosure K :=
    AdjoinRoot.liftAlgHom (cyclotomic n R) (Algebra.ofId R (AlgebraicClosure K)) a
      (by simpa [eval₂_eq_eval_map, map_cyclotomic, IsRoot.def] using ha)
  exact ⟨Algebra.TensorProduct.liftEquivRight R K (Cover R n) (AlgebraicClosure K) f⟩

/-- A selected actual map on the same scalar-extension algebra. -/
def geometricPoint : GenericFibre R n K →ₐ[K] AlgebraicClosure K :=
  Classical.choice (exists_geometricPoint R n K)

/-- The actual primitive root on this geometric fibre, using its literal map. -/
def geometricRoot : rootsOfUnity n (AlgebraicClosure K) :=
  fieldRoot R n (AlgebraicClosure K)
    (genericPointRestriction R n K (AlgebraicClosure K) (geometricPoint R n K))

theorem geometricRoot_primitive (hunit : IsUnit (n : R)) :
    IsPrimitiveRoot ((geometricRoot R n K : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) n :=
  fieldRoot_primitive R n (AlgebraicClosure K) hunit _

end GeometricPoint

/-- At n=1 the actual quotient root is 1. -/
theorem root_levelOne : root R 1 = 1 := by
  simpa using root_pow R 1

/-- The degree-one cover is literally isomorphic to the base algebra. -/
def levelOneEquiv : Cover R 1 ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom (cyclotomic 1 R) (AlgHom.id R R) 1 (by simp))
    (Algebra.ofId R (Cover R 1))
    (by ext)
    (by
      apply AdjoinRoot.algHom_ext
      simp [root_levelOne])

end AlgebraicGeometry.Scheme.Group.PrimitiveRootCover
