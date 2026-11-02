/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.FractionRing
public import Aglib.RingTheory.MvPowerSeries.FiniteCoefficientExpansion.Differentials
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.FractionRing


/-!
# The original expanded-base fraction-field square

`K₀` is the fraction field of the base series ring, while `K` is the
fraction field of the original larger series ring. The latter is localized
as an A-algebra at the image of the nonzero base elements. The exact
induced field map transports the constructed nonzero algebraic differential.
-/

@[expose] public noncomputable section

open Module

-- The selected algebra maps, rather than an independently inferred Ore action,
-- determine all scalar towers in this original fraction-field square.
attribute [local instance 2000] Algebra.toSMul

local instance {F : Type*} [Field F] : IsDomain (MvPowerSeries (Fin 2) F) :=
  NoZeroDivisors.to_isDomain _


open KaehlerDifferential

namespace IsFractionRing

/-- Powers in the original scalar image make the actual fraction field a localization
at the image of the base's nonzero elements. -/
theorem isLocalization_of_power_mem_range
    {R A K : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field K] [Algebra R A] [Algebra A K] [IsFractionRing A K]
    (q : ℕ) (hq : q ≠ 0) (hinj : Function.Injective (algebraMap R A))
    (hpow : ∀ a : A, ∃ r : R, algebraMap R A r = a ^ q) :
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) K := by
  classical
  let T := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  apply (isLocalization_iff T K).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    apply isUnit_iff_ne_zero.mpr
    have hsA : (s : A) ≠ 0 := by
      obtain ⟨r, hr, hrs⟩ := s.property
      intro hs
      have hr0 : r = 0 := hinj (by simpa only [map_zero] using hrs.trans hs)
      exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hr0
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hsA
  · intro z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) z
    obtain ⟨r, hr⟩ := hpow (b : A)
    have hb : (b : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
    have hr0 : r ≠ 0 := by
      intro h
      apply pow_ne_zero q hb
      rw [← hr, h, map_zero]
    let t : T := ⟨algebraMap R A r,
      Algebra.mem_algebraMapSubmonoid_of_mem ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr0⟩⟩
    refine ⟨⟨a * (b : A) ^ (q - 1), t⟩, ?_⟩
    change z * algebraMap A K (algebraMap R A r) =
      algebraMap A K (a * (b : A) ^ (q - 1))
    have hqpow : (b : A) ^ q = (b : A) * (b : A) ^ (q - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]
    rw [hr, hqpow, map_mul, ← mul_assoc, hab, ← map_mul]
  · intro x y h
    refine ⟨1, ?_⟩
    simpa only [Submonoid.coe_one, one_mul] using (IsFractionRing.injective A K h)

end IsFractionRing

namespace MvPowerSeries
namespace FiniteCoefficientExpansion

variable {E k : Type*} [Field E] [Field k] [Algebra E k]

theorem scalarMap_injective (q : ℕ) (hq : q ≠ 0) :
    Function.Injective (scalarMap (k₀ := E) (k := k) q hq) := by
  intro f g h
  apply MvPowerSeries.ext
  intro n
  apply (algebraMap E k).injective
  have hn := congrArg (coeff (q • n)) h
  simpa only [scalarMap_apply, coeff_expand_smul, coeff_map] using hn

/-- The original base series map followed by the original fraction-ring inclusion. -/
def seriesFractionMap (q : ℕ) (hq : q ≠ 0) :
    MvPowerSeries (Fin 2) E →+* FractionRing (MvPowerSeries (Fin 2) k) :=
  (algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))).comp
    (scalarMap q hq)

theorem seriesFractionMap_injective (q : ℕ) (hq : q ≠ 0) :
    Function.Injective (seriesFractionMap (E := E) (k := k) q hq) :=
  (IsFractionRing.injective (MvPowerSeries (Fin 2) k) _).comp (scalarMap_injective q hq)

/-- The actual induced inclusion of the two distinct fraction fields. -/
def fractionBaseMap (q : ℕ) (hq : q ≠ 0) :
    FractionRing (MvPowerSeries (Fin 2) E) →+* FractionRing (MvPowerSeries (Fin 2) k) :=
  IsFractionRing.lift (seriesFractionMap_injective (E := E) (k := k) q hq)

@[simp]
theorem fractionBaseMap_algebraMap (q : ℕ) (hq : q ≠ 0) (f : MvPowerSeries (Fin 2) E) :
    fractionBaseMap (k := k) q hq
        (algebraMap _ (FractionRing (MvPowerSeries (Fin 2) E)) f) =
      algebraMap _ (FractionRing (MvPowerSeries (Fin 2) k)) (scalarMap (k := k) q hq f) :=
  IsFractionRing.lift_algebraMap _ f

/-- The original expanded-series scalar action on the actual fraction field. -/
@[instance_reducible]
def seriesFractionAlgebra (q : ℕ) (hq : q ≠ 0) :
    Algebra (MvPowerSeries (Fin 2) E) (FractionRing (MvPowerSeries (Fin 2) k)) :=
  (seriesFractionMap (E := E) (k := k) q hq).toAlgebra

/-- The fraction-field scalar action induced by the same original expansion map. -/
@[instance_reducible]
def fractionBaseAlgebra (q : ℕ) (hq : q ≠ 0) :
    Algebra (FractionRing (MvPowerSeries (Fin 2) E))
      (FractionRing (MvPowerSeries (Fin 2) k)) :=
  (fractionBaseMap (E := E) (k := k) q hq).toAlgebra

theorem seriesFraction_isScalarTower (q : ℕ) (hq : q ≠ 0) :
    letI := scalarAlgebra (k₀ := E) (k := k) q hq
    letI := seriesFractionAlgebra (E := E) (k := k) q hq
    IsScalarTower (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)
      (FractionRing (MvPowerSeries (Fin 2) k)) := by
  let := scalarAlgebra (k₀ := E) (k := k) q hq
  let := seriesFractionAlgebra (E := E) (k := k) q hq
  exact IsScalarTower.of_algebraMap_eq (R := MvPowerSeries (Fin 2) E)
    (S := MvPowerSeries (Fin 2) k)
    (A := FractionRing (MvPowerSeries (Fin 2) k)) fun _ => rfl

theorem fractionBase_isScalarTower (q : ℕ) (hq : q ≠ 0) :
    letI := seriesFractionAlgebra (E := E) (k := k) q hq
    letI := fractionBaseAlgebra (E := E) (k := k) q hq
    IsScalarTower (MvPowerSeries (Fin 2) E) (FractionRing (MvPowerSeries (Fin 2) E))
      (FractionRing (MvPowerSeries (Fin 2) k)) := by
  let := seriesFractionAlgebra (E := E) (k := k) q hq
  let := fractionBaseAlgebra (E := E) (k := k) q hq
  exact IsScalarTower.of_algebraMap_eq (R := MvPowerSeries (Fin 2) E)
    (S := FractionRing (MvPowerSeries (Fin 2) E))
    (A := FractionRing (MvPowerSeries (Fin 2) k))
    fun f => (fractionBaseMap_algebraMap (k := k) q hq f).symm

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The coefficients are the actual pth powers, in the specified original subfield. -/
def frobeniusBaseSeries (F : Subfield k) (hF : (frobenius k p).fieldRange ≤ F)
    (f : MvPowerSeries (Fin 2) k) : MvPowerSeries (Fin 2) F :=
  fun n => Subfield.frobeniusCoefficient p F hF (coeff n f)

theorem scalarMap_frobeniusBaseSeries (F : Subfield k)
    (hF : (frobenius k p).fieldRange ≤ F) (f : MvPowerSeries (Fin 2) k) :
    scalarMap p (Fact.out : p.Prime).ne_zero (frobeniusBaseSeries p F hF f) = f ^ p := by
  have hm : MvPowerSeries.map (algebraMap F k) (frobeniusBaseSeries p F hF f) =
      MvPowerSeries.map (frobenius k p) f := by
    apply MvPowerSeries.ext
    intro n
    rfl
  rw [scalarMap_apply, hm, ← map_expand, map_frobenius_expand]

/-- The actual larger fraction field is localized as an A-algebra, not as a fraction field of Λ. -/
theorem fraction_isLocalization_image (F : Subfield k)
    (hF : (frobenius k p).fieldRange ≤ F) :
    letI := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
    IsLocalization
      (Algebra.algebraMapSubmonoid (MvPowerSeries (Fin 2) k)
        (nonZeroDivisors (MvPowerSeries (Fin 2) F)))
      (FractionRing (MvPowerSeries (Fin 2) k)) := by
  let := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
  apply IsFractionRing.isLocalization_of_power_mem_range p (Fact.out : p.Prime).ne_zero
    (scalarMap_injective p (Fact.out : p.Prime).ne_zero)
  intro f
  exact ⟨frobeniusBaseSeries p F hF f, scalarMap_frobeniusBaseSeries p F hF f⟩

/-- A nonzero differential in the constructed ordinary basis stays nonzero
over the original K/K₀. -/
theorem fraction_D_ne_zero {ι : Type*} (F : Subfield k)
    (hF : (frobenius k p).fieldRange ≤ F) :
    letI := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
    letI := seriesFractionAlgebra (E := F) (k := k) p (Fact.out : p.Prime).ne_zero
    letI := fractionBaseAlgebra (E := F) (k := k) p (Fact.out : p.Prime).ne_zero
    ∀ (_b : Basis ι (MvPowerSeries (Fin 2) k)
      (KaehlerDifferential (MvPowerSeries (Fin 2) F) (MvPowerSeries (Fin 2) k)))
      (f : MvPowerSeries (Fin 2) k),
      KaehlerDifferential.D (MvPowerSeries (Fin 2) F) (MvPowerSeries (Fin 2) k) f ≠ 0 →
      KaehlerDifferential.D (FractionRing (MvPowerSeries (Fin 2) F))
        (FractionRing (MvPowerSeries (Fin 2) k))
        (algebraMap _ (FractionRing (MvPowerSeries (Fin 2) k)) f) ≠ 0 := by
  let := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
  let := seriesFractionAlgebra (E := F) (k := k) p (Fact.out : p.Prime).ne_zero
  let := fractionBaseAlgebra (E := F) (k := k) p (Fact.out : p.Prime).ne_zero
  let := seriesFraction_isScalarTower (E := F) (k := k) p (Fact.out : p.Prime).ne_zero
  let := fractionBase_isScalarTower (E := F) (k := k) p (Fact.out : p.Prime).ne_zero
  let := fraction_isLocalization_image p F hF
  intro b f hf
  apply KaehlerDifferential.map_D_ne_zero_of_basis_localization
    (nonZeroDivisors (MvPowerSeries (Fin 2) F)) b ?_ f hf
  intro s
  have hs : (s : MvPowerSeries (Fin 2) F) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp s.property
  change scalarMap (k := k) p (Fact.out : p.Prime).ne_zero
    (s : MvPowerSeries (Fin 2) F) ≠ 0
  simpa only [map_zero] using
    (scalarMap_injective (E := F) (k := k) p (Fact.out : p.Prime).ne_zero).ne hs

/-- The fixed non-pth-power series keeps its constructed coefficient-field branch after passing
to the two original fraction fields. -/
theorem exists_singleSeries_fraction_base (f : MvPowerSeries (Fin 2) k)
    (hf : ¬ ∃ g : MvPowerSeries (Fin 2) k, g ^ p = f) :
    (letI := fractionBaseAlgebra (E := (⊤ : Subfield k)) (k := k)
        p (Fact.out : p.Prime).ne_zero;
      KaehlerDifferential.D (FractionRing (MvPowerSeries (Fin 2) (⊤ : Subfield k)))
        (FractionRing (MvPowerSeries (Fin 2) k))
        (algebraMap _ (FractionRing (MvPowerSeries (Fin 2) k)) f) ≠ 0) ∨
    ∃ n : Fin 2 →₀ ℕ, ∃ F : Subfield k,
      ∃ _hF : Maximal (fun G : Subfield k => (frobenius k p).fieldRange ≤ G ∧ coeff n f ∉ G) F,
      (letI := fractionBaseAlgebra (E := F) (k := k) p (Fact.out : p.Prime).ne_zero;
        KaehlerDifferential.D (FractionRing (MvPowerSeries (Fin 2) F))
          (FractionRing (MvPowerSeries (Fin 2) k))
          (algebraMap _ (FractionRing (MvPowerSeries (Fin 2) k)) f) ≠ 0) := by
  obtain h | ⟨n, F, hF, h⟩ := exists_singleSeries_base p f hf
  · left
    let := scalarAlgebra (k₀ := (⊤ : Subfield k)) (k := k) p (Fact.out : p.Prime).ne_zero
    let := seriesFractionAlgebra (E := (⊤ : Subfield k)) (k := k) p (Fact.out : p.Prime).ne_zero
    let := fractionBaseAlgebra (E := (⊤ : Subfield k)) (k := k) p (Fact.out : p.Prime).ne_zero
    have hs : Function.Surjective (algebraMap (⊤ : Subfield k) k) :=
      fun x => ⟨⟨x, by simp⟩, rfl⟩
    exact fraction_D_ne_zero p (⊤ : Subfield k) le_top (twoVariableBasis p hs) f h
  · refine Or.inr ⟨n, F, hF, ?_⟩
    let := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
    let := seriesFractionAlgebra (E := F) (k := k) p (Fact.out : p.Prime).ne_zero
    let := fractionBaseAlgebra (E := F) (k := k) p (Fact.out : p.Prime).ne_zero
    exact fraction_D_ne_zero p F hF.prop.1
      (nonPowerDifferentialBasis p F (coeff n f) hF) f h

end FiniteCoefficientExpansion
end MvPowerSeries


namespace MvPowerSeries.FiniteCoefficientExpansion

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The finite series entrance and its actual fraction field retain one expanded base.
The coefficient field is chosen once, and the generic rank is strictly positive. -/
theorem exists_singleSeries_fraction_basis (f : MvPowerSeries (Fin 2) k)
    (hf : ¬ ∃ g : MvPowerSeries (Fin 2) k, g ^ p = f) :
    ∃ E : Subfield k, ∃ r : ℕ, 0 < r ∧
      (letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero;
        letI := seriesFractionAlgebra (E := E) (k := k) p (Fact.out : p.Prime).ne_zero;
        Module.Finite (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k) ∧
        Nonempty (Module.Basis (Fin r) (MvPowerSeries (Fin 2) k)
          (KaehlerDifferential (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k))) ∧
        Module.finrank (FractionRing (MvPowerSeries (Fin 2) k))
          (KaehlerDifferential (MvPowerSeries (Fin 2) E)
            (FractionRing (MvPowerSeries (Fin 2) k))) = r ∧
        KaehlerDifferential.D (MvPowerSeries (Fin 2) E)
          (FractionRing (MvPowerSeries (Fin 2) k))
          (algebraMap _ (FractionRing (MvPowerSeries (Fin 2) k)) f) ≠ 0) := by
  obtain ⟨E, r, hr, hfinite, ⟨b⟩, hdf⟩ := exists_singleSeries_finite_basis p f hf
  refine ⟨E, r, hr, ?_⟩
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  let := seriesFractionAlgebra (E := E) (k := k) p (Fact.out : p.Prime).ne_zero
  let := seriesFraction_isScalarTower (E := E) (k := k) p (Fact.out : p.Prime).ne_zero
  refine ⟨hfinite, ⟨b⟩, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      KaehlerDifferential.finrank_fraction_of_basis
        (K := FractionRing (MvPowerSeries (Fin 2) k)) b
  · exact KaehlerDifferential.fraction_D_ne_zero_of_basis b f hdf

end MvPowerSeries.FiniteCoefficientExpansion
