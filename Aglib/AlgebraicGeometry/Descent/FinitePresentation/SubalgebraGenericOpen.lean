/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Dominant.Spec
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.RingTheory.Spectrum.Prime.BasicOpenUnit
public import Mathlib.RingTheory.Adjoin.FG

/-! # Original coefficient stages inside an actual generic open

The complete inverse-adjoining construction formerly specialized to integer
coefficients is used over any coefficient ring. Its original subalgebra,
ambient field, inclusion and generic open are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

/-- A generic open of the spectrum of a finitely generated coefficient subalgebra contains
the image of a larger finitely generated coefficient subalgebra. Adjoining one inverse keeps
all original coefficients and the same ambient field. -/
theorem exists_fg_coefficient_subalgebra_map_into_generic_open
    {R : Type v} {K : Type u} [CommRing R] [Field K] [Algebra R K]
    (A : Subalgebra R K) (hA : A.FG)
    (U : (Spec (.of A)).Opens) (hU : genericPoint (Spec (.of A)) ∈ U) :
    ∃ (S : Subalgebra R K) (hAS : A ≤ S), S.FG ∧
      Set.range (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAS).toRingHom)) ⊆ U := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let : IsDominant g := specMap_dominant_of_injective _ Subtype.val_injective
  let y : Spec (.of K) := ⟨⊥, inferInstance⟩
  have hgy : g y = genericPoint (Spec (.of A)) := by
    rw [Subsingleton.elim y (genericPoint (Spec (.of K)))]
    exact Scheme.map_genericPoint_of_isDominant _ g
  have hy : g y ∈ U := hgy.symm ▸ hU
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hy
  have hr0 : (r : K) ≠ 0 := by
    change ¬ (algebraMap A K r) ∈ (⊥ : Ideal K) at hr
    change algebraMap A K r ≠ 0
    simpa only [Ideal.mem_bot] using hr
  let S := A ⊔ Algebra.adjoin R ({(r : K)⁻¹} : Set K)
  have hAS : A ≤ S := le_sup_left
  have hS : S.FG := hA.sup (by
    simpa only [Finset.coe_singleton] using
      (Subalgebra.fg_adjoin_finset (R := R) ({(r : K)⁻¹} : Finset K)))
  let φ := (Subalgebra.inclusion hAS).toRingHom
  have hmem : (r : K)⁻¹ ∈ S :=
    (show Algebra.adjoin R ({(r : K)⁻¹} : Set K) ≤ S from le_sup_right)
      (Algebra.subset_adjoin (by simp))
  have hunit : IsUnit (φ r) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(r : K)⁻¹, hmem⟩, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ hr0
  refine ⟨S, hAS, hS, ?_⟩
  rintro z ⟨y, rfl⟩
  apply hsub
  change y ∈ PrimeSpectrum.basicOpen (φ r)
  rw [PrimeSpectrum.basicOpen_unit (φ r) hunit]
  trivial


end AlgebraicGeometry.Scheme
