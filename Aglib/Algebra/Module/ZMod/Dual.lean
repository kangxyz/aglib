/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.Injective
public import Aglib.Algebra.Module.Injective.Dual

/-!
# Exact dualization over every positive ZMod ring

The proved self-injectivity of the original `ZMod n` ring specializes the generic
exact native dual-map construction. This includes modulus one and composite
moduli, and applies to arbitrary module carriers at independent universes.
The only modulus premise is `n ≠ 0`; no finite-module premise is imposed.
-/

@[expose] public noncomputable section

namespace ZMod

variable (n : ℕ) [NeZero n]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module (ZMod n) M] [Module (ZMod n) N] [Module (ZMod n) P]

/-- Restriction along an injective map is surjective on the original ZMod-linear dual. -/
theorem dualMap_surjective (f : M →ₗ[ZMod n] N) (hf : Function.Injective f) :
    Function.Surjective f.dualMap := by
  let := injective_self n
  exact Module.Injective.dualMap_surjective f hf

/-- The original ZMod-linear dual reverses every exact pair. -/
theorem dualMap_exact (f : M →ₗ[ZMod n] N) (g : N →ₗ[ZMod n] P)
    (hfg : Function.Exact f g) : Function.Exact g.dualMap f.dualMap := by
  let := injective_self n
  exact Module.Injective.dualMap_exact f g hfg

/-- The original ZMod-linear dual reverses every short exact sequence. -/
theorem dualMap_shortExact (f : M →ₗ[ZMod n] N) (g : N →ₗ[ZMod n] P)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective g.dualMap ∧ Function.Exact g.dualMap f.dualMap ∧
      Function.Surjective f.dualMap := by
  let := injective_self n
  exact Module.Injective.dualMap_shortExact f g hf hfg hg

end ZMod
