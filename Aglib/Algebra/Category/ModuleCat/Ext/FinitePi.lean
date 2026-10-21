/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.LinearEquiv
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.RingTheory.Length

/-!
# Ext of a finite power and its length

The native categorical biproduct is compared to the actual finite Pi-module,
with R-linear Ext transport throughout. The length identity holds in ENat
without an unstated finiteness or cancellation assumption.
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace ModuleCat

variable (R : Type u) [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

/-- Ext in its first variable turns an actual finite power into the finite
power of the original Ext module, preserving its R-linear structure. -/
def extFinPiLinearEquiv (M N : ModuleCat.{u} R) (r n : ℕ) :
    Ext.{w} (ModuleCat.of R (Fin r → M)) N n ≃ₗ[R] (Fin r → Ext.{w} M N n) :=
  (Ext.precompLinearEquiv R (ModuleCat.biproductIsoPi (fun _ : Fin r => M)) N n).trans
    (Ext.biproductLinearEquiv R (biproduct.isBilimit (fun _ : Fin r => M)) N n)

/-- The finite-power length identity, including infinite lengths and r = 0. -/
theorem length_ext_finPi (M N : ModuleCat.{u} R) (r n : ℕ) :
    Module.length R (Ext.{w} (ModuleCat.of R (Fin r → M)) N n) =
      r * Module.length R (Ext.{w} M N n) := by
  rw [(extFinPiLinearEquiv R M N r n).length_eq]
  simp [Module.length_pi_of_fintype, nsmul_eq_mul]

end ModuleCat
