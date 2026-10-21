/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationPrecision
public import Aglib.RingTheory.AdicCompletion.Congruence
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # The native completion of polynomial-local henselization

The equivalence is the composite of the already constructed genuine completion
maps. Its restriction is the original formal-series map, and its quotient
coordinates are the original native `AdicCompletion.evalₐ` maps.
-/

@[expose] public section
noncomputable section

open IsLocalRing

namespace PolynomialLocalHenselization

universe u
variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)

local notation "H" => PolynomialLocalHenselization R n
local notation "L" => PolynomialLocalRing R n
local notation "C" => PolynomialLocalRing.FormalSeries R n
local notation "Hhat" => AdicCompletion (maximalIdeal H) H

/-- The actual native completion, not a replacement chosen up to isomorphism. -/
def completionFormalEquiv : Hhat ≃ₐ[R] C :=
  ((Henselization.completionEquiv L).symm.restrictScalars R).trans
    (PolynomialLocalRing.completionEquiv R n)

/-- The exact square with the original henselization-to-formal-series map. -/
@[simp] theorem completionFormalEquiv_algebraMap (x : H) :
    completionFormalEquiv R n (algebraMap H Hhat x) = toFormalSeries R n x := by
  have h := AlgHom.congr_fun (Henselization.completionMapInv_comp_of L) x
  change Henselization.completionMapInv L (algebraMap H Hhat x) =
    Henselization.toAdicCompletion L x at h
  change PolynomialLocalRing.completionEquiv R n
    (Henselization.completionMapInv L (algebraMap H Hhat x)) = _
  rw [h]
  exact AlgHom.congr_fun (completionFormalMap_eq_toFormalSeries R n) x

/-- Its finite quotient coordinates use the original completion projections. -/
theorem mk_completionFormalEquiv (c : ℕ) (z : Hhat) :
    Ideal.Quotient.mk (maximalIdeal C ^ c) (completionFormalEquiv R n z) =
      PolynomialLocalRing.localMixedQuotientEquiv R n c
        ((Henselization.quotientMaximalIdealPowEquivAll L c).symm
          (AdicCompletion.evalₐ (maximalIdeal H) c z)) := by
  change Ideal.Quotient.mk _ (PolynomialLocalRing.completionToFormal R n
    (Henselization.completionMapInv L z)) = _
  rw [PolynomialLocalRing.mk_completionToFormal, Henselization.eval_completionMapInv]

/-- Formal precision is exactly native quotient equality, also at order zero. -/
theorem completionFormalEquiv_sub_mem_iff (c : ℕ) (z w : Hhat) :
    completionFormalEquiv R n z - completionFormalEquiv R n w ∈
        maximalIdeal C ^ c ↔
      AdicCompletion.evalₐ (maximalIdeal H) c z =
        AdicCompletion.evalₐ (maximalIdeal H) c w := by
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    mk_completionFormalEquiv, mk_completionFormalEquiv]
  exact (PolynomialLocalRing.localMixedQuotientEquiv R n c).injective.eq_iff.trans
    (Henselization.quotientMaximalIdealPowEquivAll L c).symm.injective.eq_iff

/-- Finite generation uses only the base maximal ideal, not Noetherianity of H. -/
theorem maximalIdeal_fg : (maximalIdeal H).FG := by
  rw [← Henselization.map_maximalIdeal L]
  exact (maximalIdeal L).fg_of_isNoetherianRing.map (algebraMap L H)

/-- Native quotient equality is the actual extended-ideal error criterion. -/
theorem native_eval_eq_iff_sub_mem (c : ℕ) (z w : Hhat) :
    AdicCompletion.evalₐ (maximalIdeal H) c z =
        AdicCompletion.evalₐ (maximalIdeal H) c w ↔
      z - w ∈ (maximalIdeal H ^ c).map (algebraMap H Hhat) :=
  AdicCompletion.evalₐ_eq_iff_sub_mem _ (maximalIdeal_fg R n) c z w

end PolynomialLocalHenselization
