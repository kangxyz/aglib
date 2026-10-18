/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.RationalResidueTower
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalFinite
public import Aglib.KTheory.MilnorK.Residue.Polynomial.CoefficientEquiv
public import Aglib.RingTheory.AdjoinRootScalarBranchCoefficientEquiv

/-!
# The full actual finite-place rational norm square

The original polynomial-root formula has the norms of its actual residue
extensions. Literal coefficient equivalences identify all branches and their
original quotient maps, transporting the formula to arbitrary finite fields.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial Polynomial.LocalResidue PolynomialResidue PolynomialNorm AdjoinRoot
open scoped RatFunc

attribute [local instance] Polynomial.algebra AdjoinRoot.scalarBranchAlgebra
  residueRootFinite residueRootCharZero primeRationalFinite

universe u

/-- The general polynomial-root square, expressed with the norms of the
original residue field extensions and their full branch sum. -/
theorem residueAt_finiteExtensionNorm_rational_root
    {k : Type u} [Field k] [CharZero k] (p h : MonicIrreducible k)
    (n : ℕ) (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    residueAt h.val n
      (finiteExtensionNorm (RatFunc k) (RatFunc (AdjoinRoot p.val)) (n + 1) x) =
      rationalResidueNormSum k (AdjoinRoot p.val) h n x := by
  classical
  let : Finite (IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val)))) :=
    finite_irreducibleBranch _ (h.property.1.map _)
  let : Fintype (IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val)))) :=
    Fintype.ofFinite _
  unfold rationalResidueNormSum
  rw [← rationalFunctionNorm_eq_finiteExtensionNorm p (n + 1)]
  refine (residueAt_rationalFunctionNorm p h n x).trans ?_
  apply Fintype.sum_equiv (placesAboveBranchEquiv (algebraMap k (AdjoinRoot p.val)) h)
  intro r
  exact tensorBranch_polynomialNorm_eq_finiteExtensionNorm p h
    (placesAboveBranchEquiv (algebraMap k (AdjoinRoot p.val)) h r) n _

/-- Literal coefficient-algebra equivalences preserve the full sum of actual
residue norms, with every mapped branch retained. -/
theorem rationalResidueNormSum_map_algEquiv
    {k A B : Type u} [Field k] [CharZero k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] [FiniteDimensional k A] [FiniteDimensional k B]
    (φ : A ≃ₐ[k] B) (h : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc A) (n + 1)) :
    rationalResidueNormSum k B h n (map (n + 1) (fractionMap φ.toRingHom) x) =
      rationalResidueNormSum k A h n x := by
  classical
  let : Finite (IrreducibleBranch (h.val.map (algebraMap k A))) :=
    finite_irreducibleBranch _ (h.property.1.map _)
  let : Fintype (IrreducibleBranch (h.val.map (algebraMap k A))) := Fintype.ofFinite _
  let : Finite (IrreducibleBranch (h.val.map (algebraMap k B))) :=
    finite_irreducibleBranch _ (h.property.1.map _)
  let : Fintype (IrreducibleBranch (h.val.map (algebraMap k B))) := Fintype.ofFinite _
  unfold rationalResidueNormSum
  symm
  apply Fintype.sum_equiv (scalarBranchCoefficientEquiv φ h.val)
  intro r
  let s := scalarBranchCoefficientEquiv φ h.val r
  let : Fact (Irreducible (r.val.val.map φ.toRingHom)) :=
    ⟨irreducible_map_ringEquiv φ.toRingEquiv r.val.val r.val.property.2⟩
  let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
    finiteDimensional_scalarBranch_residue h r
  let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot s.val.val) :=
    finiteDimensional_scalarBranch_residue h s
  change finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n
      (residueAt r.val.val n x) =
    finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot s.val.val) n
      (residueAt (r.val.val.map φ.toRingHom) n
        (map (n + 1) (fractionMapRingEquiv φ.toRingEquiv).toRingHom x))
  rw [residueAt_mapRingEquiv]
  rw [← scalarBranchCoefficientAlgEquiv_toRingHom]
  exact (finiteExtensionNorm_map_algEquiv (scalarBranchCoefficientAlgEquiv φ h.val r)
    n (residueAt r.val.val n x)).symm

/-- For every actual finite coefficient extension and every original finite
place, rational norm and residue commute through the complete actual residue
norm sum. There is no normality, degree, or supplied compatibility premise. -/
theorem residueAt_finiteExtensionNorm_rational
    {k : Type u} [Field k] [CharZero k] (E : Type u) [Field E]
    [Algebra k E] [FiniteDimensional k E] (h : MonicIrreducible k)
    (n : ℕ) (x : K (RatFunc E) (n + 1)) :
    residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc E) (n + 1) x) =
      rationalResidueNormSum k E h n x := by
  let p := finiteNormPolynomial k E
  let φ := finiteNormPresentation k E
  let ε := fractionMapAlgEquiv φ
  have hex : ∃ y : K (RatFunc (AdjoinRoot p.val)) (n + 1),
      map (n + 1) ε.toRingHom y = x := by
    refine ⟨map (n + 1) ε.symm.toRingHom x, ?_⟩
    rw [← LinearMap.comp_apply, ← map_comp]
    have hi : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id (RatFunc E) := by
      ext a
      exact ε.apply_symm_apply a
    rw [hi, map_id, LinearMap.id_apply]
  obtain ⟨y, rfl⟩ := hex
  rw [finiteExtensionNorm_map_algEquiv ε]
  change _ = rationalResidueNormSum k E h n
    (map (n + 1) (fractionMap φ.toRingHom) y)
  rw [rationalResidueNormSum_map_algEquiv]
  exact residueAt_finiteExtensionNorm_rational_root p h n y

end MilnorK
