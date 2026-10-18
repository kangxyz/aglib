/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches
public import Aglib.RingTheory.PolynomialPlaceContraction
public import Mathlib.Data.Fintype.BigOperators

/-!
# Literal polynomial branches in a coefficient-field tower

Every factor after two coefficient extensions lies over a unique factor after
the first extension. The resulting bijection retains the upper polynomial
literally, and the two original quotient maps compose to the direct map.
Neither separability nor finiteness of the coefficient extensions is needed.
-/

@[expose] public noncomputable section

open Polynomial Polynomial.LocalResidue

namespace AdjoinRoot

variable {k L E : Type*} [Field k] [Field L] [Field E]

/-- All pairs of successive literal factors in a coefficient-field tower. -/
abbrev CoefficientTowerBranch (φ : k →+* L) (ψ : L →+* E) (h : k[X]) :=
  Σ r : IrreducibleBranch (h.map φ), IrreducibleBranch (r.val.val.map ψ)

/-- A successive factor is a direct factor, with exactly the same upper polynomial. -/
def coefficientTowerBranch (φ : k →+* L) (ψ : L →+* E) (h : k[X])
    (u : CoefficientTowerBranch φ ψ h) : IrreducibleBranch (h.map (ψ.comp φ)) :=
  ⟨u.2.val, by
    rw [← Polynomial.map_map]
    exact u.2.property.trans (Polynomial.map_dvd ψ u.1.property)⟩

/-- A direct factor contracts to only one intermediate monic irreducible factor. -/
theorem coefficientTowerBranch_injective (φ : k →+* L) (ψ : L →+* E) (h : k[X]) :
    Function.Injective (coefficientTowerBranch φ ψ h) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ he
  have hq : q.val = q'.val := congrArg Subtype.val he
  have hr : r = r' := by
    apply Subtype.ext
    apply Subtype.ext
    exact monic_irreducible_eq_of_dvd_map ψ r.val.val r'.val.val q.val.val
      r.val.property.1 r'.val.property.1 q.property (by
        simpa only [hq] using q'.property)
  subst r'
  have hqq : q = q' := Subtype.ext hq
  subst q'
  rfl

/-- Every direct factor occurs in a successive pair of literal factors. -/
theorem coefficientTowerBranch_surjective (φ : k →+* L) (ψ : L →+* E)
    (h : k[X]) (hh : h ≠ 0) :
    Function.Surjective (coefficientTowerBranch φ ψ h) := by
  intro q
  obtain ⟨r, hrm, hri, hrh, hqr⟩ :=
    exists_monic_irreducible_dvd_of_dvd_map ψ q.val.val q.val.property.2
      (h.map φ) (Polynomial.map_ne_zero hh) (by
        simpa only [Polynomial.map_map] using q.property)
  refine ⟨⟨⟨⟨r, hrm, hri⟩, hrh⟩, ⟨q.val, hqr⟩⟩, ?_⟩
  rfl

/-- All successive pairs and all direct factors are in bijection, without
changing the upper quotient polynomial or dropping any factor. -/
def coefficientTowerBranchEquiv (φ : k →+* L) (ψ : L →+* E)
    (h : k[X]) (hh : h ≠ 0) :
    CoefficientTowerBranch φ ψ h ≃ IrreducibleBranch (h.map (ψ.comp φ)) :=
  Equiv.ofBijective (coefficientTowerBranch φ ψ h)
    ⟨coefficientTowerBranch_injective φ ψ h,
      coefficientTowerBranch_surjective φ ψ h hh⟩

/-- The upper polynomial, hence its original quotient field, is retained literally. -/
@[simp]
theorem coefficientTowerBranchEquiv_polynomial (φ : k →+* L) (ψ : L →+* E)
    (h : k[X]) (hh : h ≠ 0) (u : CoefficientTowerBranch φ ψ h) :
    (coefficientTowerBranchEquiv φ ψ h hh u).val.val = u.2.val.val :=
  rfl

/-- The entire direct factor sum is the entire successive factor sum. -/
theorem sum_coefficientTowerBranchEquiv (φ : k →+* L) (ψ : L →+* E)
    (h : k[X]) (hh : h ≠ 0)
    [Fintype (IrreducibleBranch (h.map φ))]
    [∀ r : IrreducibleBranch (h.map φ), Fintype (IrreducibleBranch (r.val.val.map ψ))]
    [Fintype (IrreducibleBranch (h.map (ψ.comp φ)))]
    {A : Type*} [AddCommMonoid A]
    (f : IrreducibleBranch (h.map (ψ.comp φ)) → A) :
    ∑ q, f q = ∑ r : IrreducibleBranch (h.map φ),
      ∑ q : IrreducibleBranch (r.val.val.map ψ),
        f (coefficientTowerBranchEquiv φ ψ h hh ⟨r, q⟩) := by
  rw [← (coefficientTowerBranchEquiv φ ψ h hh).sum_comp f, Fintype.sum_sigma]

section AlgebraTower

variable [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]

/-- Successive factors map to the native direct coefficient polynomial, while
the upper factor itself is retained without any equality transport. -/
def coefficientTowerBranchOfAlgebra (h : k[X])
    (u : CoefficientTowerBranch (algebraMap k L) (algebraMap L E) h) :
    IrreducibleBranch (h.map (algebraMap k E)) :=
  ⟨u.2.val, by
    rw [IsScalarTower.algebraMap_eq k L E, ← Polynomial.map_map]
    exact u.2.property.trans (Polynomial.map_dvd (algebraMap L E) u.1.property)⟩

/-- The literal native-map factor bijection for an actual coefficient-field tower. -/
def coefficientTowerBranchEquivOfAlgebra (h : k[X]) (hh : h ≠ 0) :
    CoefficientTowerBranch (algebraMap k L) (algebraMap L E) h ≃
      IrreducibleBranch (h.map (algebraMap k E)) := by
  apply Equiv.ofBijective (coefficientTowerBranchOfAlgebra (L := L) h)
  constructor
  · intro u v huv
    apply coefficientTowerBranch_injective (algebraMap k L) (algebraMap L E) h
    have hval : u.2.val = v.2.val :=
      congrArg (fun q : IrreducibleBranch (h.map (algebraMap k E)) => q.val) huv
    exact Subtype.ext hval
  · intro q
    let q' : IrreducibleBranch (h.map ((algebraMap L E).comp (algebraMap k L))) :=
      ⟨q.val, by simpa only [← IsScalarTower.algebraMap_eq k L E] using q.property⟩
    obtain ⟨u, hu⟩ := coefficientTowerBranch_surjective
      (algebraMap k L) (algebraMap L E) h hh q'
    have hval : u.2.val = q.val := congrArg
      (fun q : IrreducibleBranch
        (h.map ((algebraMap L E).comp (algebraMap k L))) => q.val) hu
    exact ⟨u, Subtype.ext hval⟩

/-- The native-map bijection leaves the upper quotient polynomial definitionally unchanged. -/
@[simp]
theorem coefficientTowerBranchEquivOfAlgebra_polynomial (h : k[X]) (hh : h ≠ 0)
    (u : CoefficientTowerBranch (algebraMap k L) (algebraMap L E) h) :
    (coefficientTowerBranchEquivOfAlgebra (L := L) h hh u).val.val = u.2.val.val :=
  rfl

/-- The complete native direct factor sum is the complete double factor sum. -/
theorem sum_coefficientTowerBranchEquivOfAlgebra (h : k[X]) (hh : h ≠ 0)
    [Fintype (IrreducibleBranch (h.map (algebraMap k L)))]
    [∀ r : IrreducibleBranch (h.map (algebraMap k L)),
      Fintype (IrreducibleBranch (r.val.val.map (algebraMap L E)))]
    [Fintype (IrreducibleBranch (h.map (algebraMap k E)))]
    {A : Type*} [AddCommMonoid A]
    (f : IrreducibleBranch (h.map (algebraMap k E)) → A) :
    ∑ q, f q = ∑ r : IrreducibleBranch (h.map (algebraMap k L)),
      ∑ q : IrreducibleBranch (r.val.val.map (algebraMap L E)),
        f (coefficientTowerBranchEquivOfAlgebra (L := L) h hh ⟨r, q⟩) := by
  rw [← (coefficientTowerBranchEquivOfAlgebra (L := L) h hh).sum_comp f,
    Fintype.sum_sigma]

end AlgebraTower

end AdjoinRoot

namespace Polynomial.LocalResidue

variable {k L E : Type*} [Field k] [Field L] [Field E]

/-- The actual quotient-field maps in a coefficient tower compose to the
actual direct quotient-field map, rather than to an unspecified embedding. -/
theorem adjoinRootMap_comp (φ : k →+* L) (ψ : L →+* E)
    (h : k[X]) (r : L[X]) (q : E[X])
    [Fact (Irreducible h)] [Fact (Irreducible r)] [Fact (Irreducible q)]
    (hr : r ∣ h.map φ) (hqr : q ∣ r.map ψ) (hq : q ∣ h.map (ψ.comp φ)) :
    (adjoinRootMap ψ r q hqr).comp (adjoinRootMap φ h r hr) =
      adjoinRootMap (ψ.comp φ) h q hq := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective x
  simp only [RingHom.comp_apply, adjoinRootMap_mk, Polynomial.map_map]

/-- The three specified quotient-field maps form an actual scalar tower. -/
theorem adjoinRootMap_isScalarTower (φ : k →+* L) (ψ : L →+* E)
    (h : k[X]) (r : L[X]) (q : E[X])
    [Fact (Irreducible h)] [Fact (Irreducible r)] [Fact (Irreducible q)]
    (hr : r ∣ h.map φ) (hqr : q ∣ r.map ψ) (hq : q ∣ h.map (ψ.comp φ)) :
    letI := (adjoinRootMap φ h r hr).toAlgebra
    letI := (adjoinRootMap ψ r q hqr).toAlgebra
    letI := (adjoinRootMap (ψ.comp φ) h q hq).toAlgebra
    IsScalarTower (AdjoinRoot h) (AdjoinRoot r) (AdjoinRoot q) := by
  let := (adjoinRootMap φ h r hr).toAlgebra
  let := (adjoinRootMap ψ r q hqr).toAlgebra
  let := (adjoinRootMap (ψ.comp φ) h q hq).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (adjoinRootMap_comp φ ψ h r q hr hqr hq).symm

/-- The same literal composition law holds on the actual local residue fields. -/
theorem residueMap_comp (φ : k →+* L) (ψ : L →+* E)
    (h : k[X]) (r : L[X]) (q : E[X])
    [Fact (Irreducible h)] [Fact (Irreducible r)] [Fact (Irreducible q)]
    (hr : r ∣ h.map φ) (hqr : q ∣ r.map ψ) (hq : q ∣ h.map (ψ.comp φ)) :
    (residueMap ψ r q hqr).comp (residueMap φ h r hr) =
      residueMap (ψ.comp φ) h q hq := by
  apply RingHom.ext
  intro x
  apply (residueEquiv q).injective
  simp only [RingHom.comp_apply, residueEquiv_residueMap]
  exact RingHom.congr_fun (adjoinRootMap_comp φ ψ h r q hr hqr hq) (residueEquiv h x)

section AlgebraTower

variable [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]

/-- Original quotient maps compose to the native direct coefficient-field map. -/
theorem adjoinRootMap_comp_algebraMap (h : k[X]) (r : L[X]) (q : E[X])
    [Fact (Irreducible h)] [Fact (Irreducible r)] [Fact (Irreducible q)]
    (hr : r ∣ h.map (algebraMap k L)) (hqr : q ∣ r.map (algebraMap L E))
    (hq : q ∣ h.map (algebraMap k E)) :
    (adjoinRootMap (algebraMap L E) r q hqr).comp
        (adjoinRootMap (algebraMap k L) h r hr) =
      adjoinRootMap (algebraMap k E) h q hq := by
  have hq' : q ∣ h.map ((algebraMap L E).comp (algebraMap k L)) := by
    simpa only [← IsScalarTower.algebraMap_eq k L E] using hq
  simpa only [← IsScalarTower.algebraMap_eq k L E] using
    adjoinRootMap_comp (algebraMap k L) (algebraMap L E) h r q hr hqr hq'

/-- The original lower, upper, and native direct quotient maps form a scalar tower. -/
theorem adjoinRootMap_isScalarTowerOfAlgebra (h : k[X]) (r : L[X]) (q : E[X])
    [Fact (Irreducible h)] [Fact (Irreducible r)] [Fact (Irreducible q)]
    (hr : r ∣ h.map (algebraMap k L)) (hqr : q ∣ r.map (algebraMap L E))
    (hq : q ∣ h.map (algebraMap k E)) :
    letI := (adjoinRootMap (algebraMap k L) h r hr).toAlgebra
    letI := (adjoinRootMap (algebraMap L E) r q hqr).toAlgebra
    letI := (adjoinRootMap (algebraMap k E) h q hq).toAlgebra
    IsScalarTower (AdjoinRoot h) (AdjoinRoot r) (AdjoinRoot q) := by
  let := (adjoinRootMap (algebraMap k L) h r hr).toAlgebra
  let := (adjoinRootMap (algebraMap L E) r q hqr).toAlgebra
  let := (adjoinRootMap (algebraMap k E) h q hq).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (adjoinRootMap_comp_algebraMap h r q hr hqr hq).symm

end AlgebraTower

end Polynomial.LocalResidue
