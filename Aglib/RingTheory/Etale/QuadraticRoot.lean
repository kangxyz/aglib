/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic.LinearCombination

/-!
# The étale quadratic-root algebra, its chosen residue point and closed-fibre algebra isomorphism.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Etale/QuadraticRoot.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3a94c80add042b7022367ff1bc102ba397c16f89a3bc441ed23ee7e827d75d10`.
-/

@[expose] public section

open Polynomial
open scoped Polynomial
universe u

section EtaleQuadraticRoot

/-! An actual pointed standard étale neighbourhood for a simple quadratic root.
No Henselian property or localness of the constructed algebra is assumed. -/
noncomputable section
open Polynomial IsLocalRing
namespace Algebra.QuadraticRoot
variable {R : Type u} [CommRing R]

/-- The auxiliary monic quadratic `X² - bX + ac` used to construct a root of `aX² + bX + c`. -/
def polynomial (a b c : R) : R[X] := X ^ 2 - C b * X + C (a * c)

/-- The standard-étale pair obtained from the auxiliary quadratic by inverting the product of
its derivative and its variable. -/
def pair (a b c : R) : StandardEtalePair R where
  f := polynomial a b c
  monic_f := by unfold polynomial; monicity!
  g := (polynomial a b c).derivative * X
  cond := ⟨X, 0, 1, by simp⟩

/-- The standard-étale algebra of the auxiliary quadratic with its derivative and universal
generator inverted. -/
abbrev RootAlgebra (a b c : R) := (pair a b c).Ring

lemma generator_isUnit (a b c : R) : IsUnit (pair a b c).X := by
  have h := (pair a b c).hasMap_X.2
  change IsUnit (aeval (pair a b c).X ((polynomial a b c).derivative * X)) at h
  rw [map_mul, aeval_X] at h
  exact isUnit_of_mul_isUnit_right h

/-- The universal generator of the standard-étale algebra, regarded as a unit. -/
def generatorUnit (a b c : R) : (RootAlgebra a b c)ˣ := (generator_isUnit a b c).unit

/-- The root `-c/t` of `aX² + bX + c` constructed from the invertible auxiliary generator `t`. -/
def root (a b c : R) : RootAlgebra a b c :=
  -algebraMap R _ c * ↑(generatorUnit a b c)⁻¹

lemma root_equation (a b c : R) :
    algebraMap R _ a * root a b c ^ 2 + algebraMap R _ b * root a b c +
      algebraMap R _ c = 0 := by
  have hz := (pair a b c).hasMap_X.1
  change aeval (pair a b c).X (polynomial a b c) = 0 at hz
  have hv : (generatorUnit a b c : RootAlgebra a b c) = (pair a b c).X :=
    (generator_isUnit a b c).unit_spec
  simp only [polynomial, map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C] at hz
  rw [← hv] at hz
  have hi := (generatorUnit a b c).mul_inv
  dsimp [root]
  linear_combination algebraMap R _ c * (↑(generatorUnit a b c)⁻¹ : RootAlgebra a b c) ^ 2 * hz -
    algebraMap R _ c * ((generatorUnit a b c : RootAlgebra a b c) *
      ↑(generatorUnit a b c)⁻¹ - algebraMap R _ b * ↑(generatorUnit a b c)⁻¹ + 1) * hi

theorem etale (a b c : R) : _root_.Algebra.Etale R (RootAlgebra a b c) := inferInstance

section Residue
variable [IsLocalRing R] (a b c : R) (hb : IsUnit b)
    (hc : c ∈ maximalIdeal R)

include hb hc in
lemma hasResidueMap : (pair a b c).HasMap (residue R b) := by
  have hcz : residue R c = 0 := (residue_eq_zero_iff _).mpr hc
  constructor
  · simp [pair, polynomial, hcz]
    ring
  · have he : aeval (residue R b) (pair a b c).g = (residue R b) ^ 2 := by
      norm_num [pair, polynomial, derivative_pow, derivative_mul]
      have htwo : (residue R) (2 : R) = (2 : ResidueField R) := map_ofNat _ _
      rw [htwo]
      ring
    rw [he]
    exact (hb.map (residue R)).pow 2

/-- The actual original-residue-field point on the constructed étale algebra. -/
def point : RootAlgebra a b c →ₐ[R] ResidueField R :=
  (pair a b c).lift (residue R b) (hasResidueMap a b c hb hc)

@[simp] lemma point_generator : point a b c hb hc (pair a b c).X = residue R b := by
  exact (pair a b c).lift_X _ _

@[simp] lemma point_root : point a b c hb hc (root a b c) = 0 := by
  have hcz : residue R c = 0 := (residue_eq_zero_iff _).mpr hc
  simp [root, map_mul, map_neg, AlgHom.commutes, hcz]

/-- The structural map and the selected point compose to the original residue map. -/
lemma point_structure (r : R) :
    point a b c hb hc (algebraMap R _ r) = residue R r :=
  (point a b c hb hc).commutes r

include hb hc in
theorem nontrivial : Nontrivial (RootAlgebra a b c) :=
  (point a b c hb hc).toRingHom.domain_nontrivial

include hb hc in
/-- Flatness and the actual original-residue point make this neighbourhood
faithfully flat; the constructed algebra is not asserted to be local. -/
theorem faithfullyFlat : Module.FaithfullyFlat R (RootAlgebra a b c) := by
  let : _root_.Algebra.Etale R (RootAlgebra a b c) := etale a b c
  refine ⟨fun m hm ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, IsLocalRing.eq_maximalIdeal hm]
  refine (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr ?_
  intro ht
  have hle : Ideal.map (algebraMap R (RootAlgebra a b c)) (maximalIdeal R) ≤
      RingHom.ker (point a b c hb hc).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change point a b c hb hc (algebraMap R _ x) = 0
    rw [point_structure]
    exact (residue_eq_zero_iff x).mpr hx
  have hone : (1 : RootAlgebra a b c) ∈ RingHom.ker (point a b c hb hc).toRingHom :=
    hle (by rw [ht]; trivial)
  change (point a b c hb hc) 1 = 0 at hone
  rw [map_one] at hone
  exact one_ne_zero hone

end Residue
end Algebra.QuadraticRoot

end
end EtaleQuadraticRoot

section EtaleRootClosedFiber

/-! The entire quotient by the extended maximal ideal of the actual quadratic
root algebra is the original residue field. This makes no localness assertion
about the root algebra itself. -/
noncomputable section
open Polynomial IsLocalRing
namespace Algebra.QuadraticRoot
variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem point_surjective (a b c : R) (hb : IsUnit b) (hc : c ∈ maximalIdeal R) :
    Function.Surjective (Algebra.QuadraticRoot.point a b c hb hc) := by
  intro x
  obtain ⟨r, hr⟩ := residue_surjective x
  exact ⟨algebraMap R _ r, (Algebra.QuadraticRoot.point_structure a b c hb hc r).trans hr⟩

/-- Exact equality with the extension of the original maximal ideal. -/
theorem point_ker (a b c : R) (hb : IsUnit b) (hc : c ∈ maximalIdeal R) :
    RingHom.ker (Algebra.QuadraticRoot.point a b c hb hc).toRingHom =
      Ideal.map (algebraMap R (Algebra.QuadraticRoot.RootAlgebra a b c)) (maximalIdeal R) := by
  let S := Algebra.QuadraticRoot.RootAlgebra a b c
  let I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  let Q := S ⧸ I
  let q : S →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let p := Algebra.QuadraticRoot.point a b c hb hc
  have hzero (r : R) (hr : r ∈ maximalIdeal R) : algebraMap R Q r = 0 := by
    change Ideal.Quotient.mk I (algebraMap R S r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  let j : ResidueField R →ₐ[R] Q := Ideal.Quotient.liftₐ (maximalIdeal R)
    (Algebra.ofId R Q) hzero
  have hz := ((Algebra.QuadraticRoot.pair a b c).hasMap_X.map q).1
  change aeval (q (Algebra.QuadraticRoot.pair a b c).X)
    (Algebra.QuadraticRoot.polynomial a b c) = 0 at hz
  simp only [Algebra.QuadraticRoot.polynomial, map_add, map_sub, map_pow, map_mul,
    aeval_X, aeval_C, hzero c hc, mul_zero, add_zero] at hz
  have hzu : IsUnit (q (Algebra.QuadraticRoot.pair a b c).X) :=
    (Algebra.QuadraticRoot.generator_isUnit a b c).map q
  have hzb : q (Algebra.QuadraticRoot.pair a b c).X = algebraMap R Q b := by
    apply sub_eq_zero.mp
    apply hzu.mul_left_cancel
    simp only [mul_zero]
    linear_combination hz
  have hmaps : q = j.comp p := by
    apply (Algebra.QuadraticRoot.pair a b c).hom_ext
    change q (Algebra.QuadraticRoot.pair a b c).X =
      j (p (Algebra.QuadraticRoot.pair a b c).X)
    rw [Algebra.QuadraticRoot.point_generator]
    exact hzb.trans (j.commutes b).symm
  have hle : I ≤ RingHom.ker p.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change p (algebraMap R S r) = 0
    rw [p.commutes, ResidueField.algebraMap_eq]
    exact (residue_eq_zero_iff _).mpr hr
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q x = 0
    change p x = 0 at hx
    rw [hmaps, AlgHom.comp_apply, hx, map_zero]
  · exact hle

/-- The actual closed-fibre quotient is canonically the original residue field. -/
def closedFiberEquiv (a b c : R) (hb : IsUnit b) (hc : c ∈ maximalIdeal R) :
    (Algebra.QuadraticRoot.RootAlgebra a b c ⧸
      Ideal.map (algebraMap R (Algebra.QuadraticRoot.RootAlgebra a b c)) (maximalIdeal R))
      ≃ₐ[R] ResidueField R :=
  (Ideal.quotientEquivAlgOfEq R (point_ker a b c hb hc).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (point_surjective a b c hb hc))

/-- The closed-fibre equivalence is induced by the actual selected residue map. -/
@[simp] theorem closedFiberEquiv_mk (a b c : R) (hb : IsUnit b)
    (hc : c ∈ maximalIdeal R) (s : Algebra.QuadraticRoot.RootAlgebra a b c) :
    closedFiberEquiv a b c hb hc (Ideal.Quotient.mk _ s) =
      Algebra.QuadraticRoot.point a b c hb hc s := by
  exact (congrArg (Ideal.quotientKerAlgEquivOfSurjective (point_surjective a b c hb hc))
    (Ideal.quotientEquivAlgOfEq_mk R (point_ker a b c hb hc).symm s)).trans
    (Ideal.quotientKerAlgEquivOfSurjective_mk (point_surjective a b c hb hc) s)

end Algebra.QuadraticRoot

end
end EtaleRootClosedFiber
