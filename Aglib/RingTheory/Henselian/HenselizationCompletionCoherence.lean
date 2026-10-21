/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationCompletionEquiv
public import Aglib.RingTheory.Henselian.HenselizationCompletion

/-!
# Compatibility of completion comparison with the canonical local map

Restricting the inverse completion comparison along the henselization's
completion map reflects units, as seen on the first quotient coordinate.
When the original ring is Noetherian, the proved local universal property
identifies this actual map with the previously constructed canonical map.
No Noetherianity of the henselization is used.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The inverse comparison restricted to the henselization is a local ring map. -/
theorem completionMapInv_comp_of_isLocalHom :
    IsLocalHom ((completionMapInv R).comp
      (IsScalarTower.toAlgHom R (Henselization R)
        (AdicCompletion (maximalIdeal (Henselization R)) (Henselization R)))).toRingHom := by
  let J := maximalIdeal (Henselization R) ^ 1
  let : HenselianLocalRing (Henselization R ⧸ J) :=
    HenselianLocalRing.quotient_maximalIdeal_pow (Henselization R) 1 one_ne_zero
  let : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  constructor
  intro x hx
  have hu := hx.map (AdicCompletion.evalₐ (maximalIdeal R) 1).toRingHom
  change IsUnit (AdicCompletion.evalₐ (maximalIdeal R) 1
    (completionMapInv R (algebraMap (Henselization R)
      (AdicCompletion (maximalIdeal (Henselization R)) (Henselization R)) x))) at hu
  rw [eval_completionMapInv] at hu
  change IsUnit ((quotientMaximalIdealPowEquivAll R 1).symm
    (AdicCompletion.evalₐ (maximalIdeal (Henselization R)) 1
      (AdicCompletion.of (maximalIdeal (Henselization R)) (Henselization R) x))) at hu
  rw [AdicCompletion.evalₐ_of] at hu
  have hv := hu.map (quotientMaximalIdealPowEquivAll R 1).toRingHom
  change IsUnit ((quotientMaximalIdealPowEquivAll R 1)
    ((quotientMaximalIdealPowEquivAll R 1).symm (Ideal.Quotient.mk J x))) at hv
  rw [AlgEquiv.apply_symm_apply] at hv
  exact (isUnit_map_iff (Ideal.Quotient.mk J) x).mp hv

/-- The comparison map restricts to the canonical local map into completion. -/
theorem completionMapInv_comp_of [IsNoetherianRing R] :
    (completionMapInv R).comp
        (IsScalarTower.toAlgHom R (Henselization R)
          (AdicCompletion (maximalIdeal (Henselization R)) (Henselization R))) =
      toAdicCompletion R := by
  let := completionMapInv_comp_of_isLocalHom R
  exact toAdicCompletion_unique R _

/-- The completion comparison commutes with the canonical map from henselization. -/
theorem completionMap_toAdicCompletion [IsNoetherianRing R] (x : Henselization R) :
    completionMap R (toAdicCompletion R x) =
      algebraMap (Henselization R)
        (AdicCompletion (maximalIdeal (Henselization R)) (Henselization R)) x := by
  have h := AlgHom.congr_fun (completionMapInv_comp_of R) x
  change completionMapInv R (algebraMap (Henselization R)
    (AdicCompletion (maximalIdeal (Henselization R)) (Henselization R)) x) =
      toAdicCompletion R x at h
  rw [← h, completionMap_completionMapInv]

end Henselization
