/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FittingIdeal.BaseChange
public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Nonvanishing of the original generic Fitting ideal

Separably generated generic fraction extensions supply the actual number of
spanning differentials, not an assumed nonzero ideal. Localization compares the
original differential module to this generic module. An injective evaluation
then preserves the resulting nonzero original Fitting ideal.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential TensorProduct

namespace KaehlerDifferential

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The differentials of a separating family span, even if the family is not
algebraically independent and is not finite. -/
theorem span_range_D_of_isSeparable_adjoin (s : Set K)
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] :
    Submodule.span K (Set.range (fun a : s => D k K (a : K))) = ⊤ := by
  let L := IntermediateField.adjoin k s
  let V := Submodule.span K (Set.range (fun a : s => D k K (a : K)))
  let : Algebra.FormallyUnramified L K :=
    Algebra.FormallyUnramified.of_isSeparable L K
  have hD (a : L) : D k K (a : K) ∈ V := by
    refine IntermediateField.adjoin_induction (F := k)
      (p := fun a _ => D k K a ∈ V) ?_ ?_ ?_ ?_ ?_ a.property
    · intro a ha
      exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
    · intro a
      rw [Derivation.map_algebraMap]
      exact V.zero_mem
    · intro a b _ _ ha hb
      rw [map_add]
      exact V.add_mem ha hb
    · intro a _ ha
      rw [Derivation.leibniz_inv]
      exact V.smul_mem _ ha
    · intro a b _ _ ha hb
      rw [Derivation.leibniz]
      exact V.add_mem (V.smul_mem _ hb) (V.smul_mem _ ha)
  have hm (z : Ω[L⁄k]) : map k k L K z ∈ V := by
    have htop : (⊤ : Submodule L Ω[L⁄k]) ≤
        (V.restrictScalars L).comap (map k k L K) := by
      rw [← span_range_derivation k L]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      change map k k L K (D k L a) ∈ V
      rw [map_D]
      exact hD a
    exact htop (Submodule.mem_top : z ∈ (⊤ : Submodule L Ω[L⁄k]))
  have hsurj : Function.Surjective (mapBaseChange k L K) := by
    intro z
    exact (exact_mapBaseChange_map k L K z).mp (Subsingleton.elim _ _)
  have ht (t : K ⊗[L] Ω[L⁄k]) : mapBaseChange k L K t ∈ V := by
    induction t using TensorProduct.inductionOn with
    | tmul a z =>
        rw [mapBaseChange_tmul]
        exact V.smul_mem a (hm z)
    | add a b ha hb =>
        rw [map_add]
        exact V.add_mem ha hb
  apply top_unique
  intro z _
  obtain ⟨t, rfl⟩ := hsurj z
  exact ht t

/-- Genuine generic separability and the actual finite transcendence degree give
`Fitt_r = top`; no supplied differential-span or Fitting hypothesis is required. -/
theorem fittingIdeal_eq_top_of_isSeparablyGenerated
    [Algebra.IsSeparablyGenerated k K] (r : ℕ)
    (hdeg : Algebra.trdeg k K = (r : Cardinal)) :
    Module.fittingIdeal K Ω[K⁄k] r = ⊤ := by
  obtain ⟨s, hs, hsep⟩ := Algebra.IsSeparablyGenerated.isSeparable (k := k) (K := K)
  let := hsep
  have hcard : Cardinal.mk s = (r : Cardinal) := hs.cardinalMk_eq_trdeg.trans hdeg
  let : Finite s := Cardinal.mk_lt_aleph0_iff.mp (by rw [hcard]; exact Cardinal.natCast_lt_aleph0)
  have hnat : Nat.card s = r := by
    simpa only [Nat.card, Cardinal.toNat_natCast] using congrArg Cardinal.toNat hcard
  exact Module.fittingIdeal_eq_top_of_span_eq_top
    (span_range_D_of_isSeparable_adjoin s) hnat.le

section OriginalFractions

variable {R B F L : Type*}
variable [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B]
variable [Field F] [Algebra R F] [IsFractionRing R F]
variable [Field L] [Algebra B L] [IsFractionRing B L]
variable [Algebra R L] [IsScalarTower R B L]
variable [Algebra F L] [IsScalarTower R F L]

/-- The original source fraction field differential comparison, with both scalar
triangles explicit. It does not choose an unrelated generic field action. -/
def originalFractionDifferentialEquiv : L ⊗[B] Ω[B⁄R] ≃ₗ[L] Ω[L⁄F] := by
  letI : Algebra.FormallyEtale B L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  letI : Algebra.FormallyEtale R F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have hbij : Function.Bijective (map R F L L) := by
    refine ⟨?_, map_surjective R F L⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map R F L x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  let e : Ω[L⁄R] ≃ₗ[L] Ω[L⁄F] := LinearEquiv.ofBijective (map R F L L) hbij
  exact (tensorKaehlerEquivOfFormallyEtale R B L).trans e

omit [IsDomain R] [IsDomain B] in
/-- The original generic Fitting ideal is nonzero at the actual transcendence
index. The field actions are required to agree with the original coefficient map. -/
theorem fittingIdeal_ne_bot_of_generic_isSeparablyGenerated
    [Algebra.EssFiniteType R B] [Algebra.IsSeparablyGenerated F L]
    (r : ℕ) (hdeg : Algebra.trdeg F L = (r : Cardinal)) :
    Module.fittingIdeal B Ω[B⁄R] r ≠ ⊥ := by
  have htop : (Module.fittingIdeal B Ω[B⁄R] r).map (algebraMap B L) = ⊤ := by
    rw [← Module.fittingIdeal_baseChange]
    rw [Module.fittingIdeal_congr
      (originalFractionDifferentialEquiv (R := R) (B := B) (F := F) (L := L))]
    exact fittingIdeal_eq_top_of_isSeparablyGenerated r hdeg
  intro hzero
  rw [hzero, Ideal.map_bot] at htop
  exact bot_ne_top htop

omit [IsDomain R] [IsDomain B] in
/-- An actual injective evaluation preserves the nonzero original Fitting ideal.
This is the nonzero input for strict improvement, derived from genuine generic
separability rather than supplied as an oracle. -/
theorem map_fittingIdeal_ne_bot_of_generic_isSeparablyGenerated
    [Algebra.EssFiniteType R B] [Algebra.IsSeparablyGenerated F L]
    {S : Type*} [CommRing S] [Algebra R S]
    (χ : B →ₐ[R] S) (hχ : Function.Injective χ)
    (r : ℕ) (hdeg : Algebra.trdeg F L = (r : Cardinal)) :
    (Module.fittingIdeal B Ω[B⁄R] r).map χ.toRingHom ≠ ⊥ := by
  rw [ne_eq, Ideal.map_eq_bot_iff_of_injective (f := χ.toRingHom) hχ]
  exact fittingIdeal_ne_bot_of_generic_isSeparablyGenerated
    (R := R) (B := B) (F := F) (L := L) r hdeg

end OriginalFractions
end KaehlerDifferential
