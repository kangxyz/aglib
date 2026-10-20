/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The literal residue field of an adic completion

Foundational residue comparison for K2-015#lem:k2015-frobenius, mathematical
source revision e73d98b1b5c1e5abcdebf7d058e436d792b87982. The encoded
result identifies the quotient at an actual height-one place with the literal
residue field of its adic completion, using the canonical residue map.
Finiteness transfers from the original quotient; no arithmetic Galois quotient
or specialization of an integral K2 class is constructed here.
-/

/-!
## Migration source

Native extraction from
`lean/R5Lab/Aglib/RingTheory/DiscreteValuationRing/AdicCompletionResidue.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`4f3c27e460df174fad7b084ef71594d2962934647ace30f5a5675c1519d3f552`.
-/

@[expose] public section

open IsDedekindDomain HeightOneSpectrum
open scoped Topology

namespace IsDedekindDomain.HeightOneSpectrum.AdicCompletionResidue

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- The ring map from `R` to the residue field of the integral adic completion at the height-one
place `v`. -/
noncomputable def integralResidueMap :
    R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue (v.adicCompletionIntegers K)).comp
    (algebraMap R (v.adicCompletionIntegers K))

theorem valuation_algebraMap (b : K) :
    Valued.v (algebraMap K (v.adicCompletion K) b) = v.valuation K b := by
  simpa only [algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply] using valuedAdicCompletion_eq_valuation' v b

theorem integralResidueMap_eq_zero_iff (a : R) :
    integralResidueMap K v a = 0 ↔ a ∈ v.asIdeal := by
  change IsLocalRing.residue (v.adicCompletionIntegers K)
    (algebraMap R (v.adicCompletionIntegers K) a) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff]
  unfold adicCompletionIntegers
  rw [Valuation.mem_maximalIdeal_iff (v.adicCompletion K)
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))]
  change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a)) < 1 ↔ _
  rw [valuation_algebraMap, v.valuation_lt_one_iff_mem]

theorem exists_integer_approximation (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((algebraMap R (v.adicCompletionIntegers K) a :
      v.adicCompletion K) - x) < 1 := by
  have hnhds : {y : v.adicCompletion K | Valued.v (y - x) < 1} ∈
      𝓝 (x : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    refine ⟨1, ?_⟩
    intro y hy
    simpa only [Set.mem_ofPred_eq, Units.val_one,
      Valuation.restrict_lt_iff_lt_embedding, map_one] using hy
  obtain ⟨b, hb⟩ := (denseRange_algebraMap K v).mem_nhds hnhds
  have hb_int : v.valuation K b ≤ 1 := by
    rw [← valuation_algebraMap K v b]
    calc
      Valued.v (algebraMap K (v.adicCompletion K) b) =
          Valued.v ((algebraMap K (v.adicCompletion K) b - x) + x) := by
            congr 1
            exact (sub_add_cancel _ _).symm
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) b - x))
          (Valued.v (x : v.adicCompletion K)) := Valued.v.map_add _ _
      _ ≤ 1 := max_le hb.le x.property
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hb_int 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a) -
      algebraMap K (v.adicCompletion K) b) < 1 := by
    rw [← map_sub, valuation_algebraMap]
    simpa only [Units.val_one] using ha
  change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a) - x) < 1
  calc
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a) - x) =
        Valued.v ((algebraMap K (v.adicCompletion K) (algebraMap R K a) -
          algebraMap K (v.adicCompletion K) b) +
          (algebraMap K (v.adicCompletion K) b - x)) := by
            congr 1
            ring
    _ ≤ max _ _ := Valued.v.map_add _ _
    _ < 1 := max_lt ha' hb

theorem integralResidueMap_surjective :
    Function.Surjective (integralResidueMap K v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K) y
  obtain ⟨a, ha⟩ := exists_integer_approximation K v x
  refine ⟨a, ?_⟩
  change IsLocalRing.residue (v.adicCompletionIntegers K)
    (algebraMap R (v.adicCompletionIntegers K) a) = IsLocalRing.residue _ x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (Valuation.mem_maximalIdeal_iff (v.adicCompletion K)
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))).mpr ha

theorem integralResidueMap_ker :
    RingHom.ker (integralResidueMap K v) = v.asIdeal := by
  ext a
  exact integralResidueMap_eq_zero_iff K v a

/-- The comparison is induced by the canonical map from the same global ring
into the same completion integer ring, followed by its literal residue map. -/
noncomputable def residueRingEquiv :
    R ⧸ v.asIdeal ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (integralResidueMap_ker K v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (integralResidueMap_surjective K v))

@[simp] theorem residueRingEquiv_mk (a : R) :
    residueRingEquiv K v (Ideal.Quotient.mk v.asIdeal a) = integralResidueMap K v a := by
  simp only [residueRingEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem residue_finite [Finite (R ⧸ v.asIdeal)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  Finite.of_surjective (residueRingEquiv K v) (residueRingEquiv K v).surjective

end IsDedekindDomain.HeightOneSpectrum.AdicCompletionResidue
