/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.NormalExtension
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.HeightOneResidues
public import Aglib.RingTheory.LocalRing.FiniteCompleteRegularSubring
public import Aglib.RingTheory.Nagata.Finite
public import Aglib.RingTheory.Nagata.FiniteTypeField
public import Aglib.RingTheory.RegularLocalRing.Normal

/-!
# Finite normalization of complete Noetherian local domains

Induction on a finite dimension bound supplies normalization finiteness for
actual height-one prime quotients, which need not be normal, in their actual
finite residue-field extensions, which need not be purely inseparable.
The height-one construction gives the normal purely inseparable case; the
original normal hull and trace give every finite extension. The actual
finite complete regular subring then treats the arbitrary domain.

Rings and extension fields are in one universe, with Japanese test universe zero.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped nonZeroDivisors

universe u

namespace integralClosure

attribute [local instance] heightOneAtPrimeAlgebra heightOneAtPrimeFractionAlgebra
  atPrimeResidueQuotientAlgebra

private theorem japanese_normal_of_lower_dimension
    (d : ℕ)
    (ih : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
      [IsAdicComplete (maximalIdeal A) A], ringKrullDim A ≤ (d : ℕ) → IsJapaneseRing.{u, 0} A)
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] [IsAdicComplete (maximalIdeal R) R]
    (hd : ringKrullDim R ≤ ((d + 1 : ℕ) : ℕ∞)) : IsJapaneseRing.{u, 0} R := by
  intro L _ _ _ _ _
  apply finite_of_finite_pure_extensions R (FractionRing R) L
  intro E _ _ _ _ _ _
  let K := FractionRing R
  let : Module.IsTorsionFree R E := .trans_faithfulSMul R K E
  apply finite_of_complete_local_normal_of_finite_heightOneResidueNormalization R K E
  intro p hp hheight
  let : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_height_one p (Localization.AtPrime p) hheight
  let A := Localization.AtPrime p
  let T := integralClosure A E
  let C := R ⧸ p
  let : IsDiscreteValuationRing T := isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A T) := algebraMap_isLocalHom A K E
  let ℓ := ResidueField T
  change Module.Finite C (integralClosure C ℓ)
  let : IsNoetherianRing C := isNoetherianRing_of_surjective R C
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective
  let : IsAdicComplete (maximalIdeal C) C := by
    have h := IsAdicComplete.map_algebraMap_of_finite R (maximalIdeal R) C
    rwa [IsLocalRing.map_maximalIdeal_of_surjective
      (algebraMap R C) Ideal.Quotient.mk_surjective] at h
  let : Algebra p.ResidueField ℓ := purelyInseparableResidueAlgebra A K E
  let : IsScalarTower C p.ResidueField ℓ := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap R ℓ r =
      algebraMap p.ResidueField ℓ (algebraMap R p.ResidueField r)
    exact IsScalarTower.algebraMap_apply R p.ResidueField ℓ r
  let : Module.Finite p.ResidueField ℓ := finite_residueField_of_isPurelyInseparable A K E
  have hpne : p ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hheight
    exact zero_ne_one hheight
  obtain ⟨x, hxp, hx⟩ := p.ne_bot_iff.mp hpne
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hxp)
  have hdimC : ringKrullDim C ≤ (d : ℕ) := by
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    convert hdrop.trans hd using 1; simp
  exact (ih C hdimC).finite_integralClosure_of_isFractionRing p.ResidueField ℓ

end integralClosure

/-- Complete Noetherian local domains of any finite dimension bound are Japanese.
The induction hypothesis is used only at a genuinely lower-dimensional prime quotient. -/
theorem IsJapaneseRing.of_complete_local_dimLE (d : ℕ)
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (hd : ringKrullDim A ≤ (d : ℕ)) :
    IsJapaneseRing.{u, 0} A := by
  induction d generalizing A with
  | zero =>
    let : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr hd
    let : Field A := (Ring.KrullDimLE.isField_of_isDomain (R := A)).toField
    exact IsJapaneseRing.of_field A
  | succ d ih =>
    have hheight : (maximalIdeal A).height ≤ (d + 1 : ℕ) := by
      apply WithBot.coe_le_coe.mp
      rwa [maximalIdeal_height_eq_ringKrullDim]
    have hfinite : (maximalIdeal A).height ≠ ⊤ := ne_top_of_le_ne_top (by simp) hheight
    let e := (maximalIdeal A).height.toNat
    have he : ringKrullDim A = (e : ℕ) := by
      rw [← maximalIdeal_height_eq_ringKrullDim, ← ENat.natCast_toNat hfinite]
      rfl
    obtain ⟨R, hR, hD, hcomplete, hdR, f, hinj, _, hfin⟩ :=
      IsLocalRing.exists_finite_complete_regular_subring_of_dimension A e he
    let : IsRegularLocalRing R := hR
    let : IsDomain R := hD
    let : IsAdicComplete (maximalIdeal R) R := hcomplete
    let : IsIntegrallyClosed R := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal R
    let : Algebra R A := f.toAlgebra
    let : Module.Finite R A := hfin
    have hdimR : ringKrullDim R ≤ ((d + 1 : ℕ) : ℕ∞) :=
      (hdR.trans he.symm).le.trans hd
    have hJapanese := integralClosure.japanese_normal_of_lower_dimension d
      (fun B _ _ _ _ _ hB ↦ ih B hB) R hdimR
    exact hJapanese.of_finite hinj

/-- Every complete Noetherian local domain is Japanese, with its original
fraction-field action and auxiliary test universe zero. -/
theorem IsJapaneseRing.of_complete_local
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] : IsJapaneseRing.{u, 0} A := by
  apply IsJapaneseRing.of_complete_local_dimLE (maximalIdeal A).spanFinrank A
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast (maximalIdeal A).height_le_spanFinrank (maximalIdeal.isMaximal A).ne_top

/-- The literal normalization in every finite extension of any supplied actual
fraction field of a complete Noetherian local domain is finite. -/
theorem integralClosure.finite_of_complete_local
    (A K L : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] : Module.Finite A (integralClosure A L) :=
  (IsJapaneseRing.of_complete_local A).finite_integralClosure_of_isFractionRing K L
