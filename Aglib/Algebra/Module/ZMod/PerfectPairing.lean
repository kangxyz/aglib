/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.FiniteDual
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Perfect-pairing criteria for finite ZMod modules

For finite modules over every positive ZMod ring, a native bilinear pairing is
perfect exactly when its map to either native dual is bijective. Equal finite
cardinality reduces this to injectivity in one argument; injectivity in both
arguments also suffices. The result uses the original `LinearMap.IsPerfPair`,
its original `toPerfPair` maps and the proved native double-dual evaluation.
No primality, free-module, basis, or alternating-form assumption is introduced.

Sources: Mathlib `LinearAlgebra/PerfectPairing/Basic.lean`,
`LinearMap.IsPerfPair.of_bijective`; `ZMod/FiniteDual` for actual finite duality.
-/

@[expose] public noncomputable section

namespace ZMod

variable (n : ℕ) [NeZero n]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (ZMod n) M] [Module (ZMod n) N]

/-- For a finite right-hand module, bijectivity into its native dual is perfectness. -/
theorem isPerfPair_iff_bijective [Finite N] (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n) :
    B.IsPerfPair ↔ Function.Bijective B := by
  let := isReflexive_of_finite n N
  exact ⟨fun h => h.bijective_left, fun h => LinearMap.IsPerfPair.of_bijective B h⟩

/-- The corresponding criterion in the other argument uses the original flipped pairing. -/
theorem isPerfPair_iff_flip_bijective [Finite M] (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n) :
    B.IsPerfPair ↔ Function.Bijective B.flip := by
  constructor
  · exact fun h => h.bijective_right
  · intro h
    exact ((isPerfPair_iff_bijective n B.flip).mpr h).flip

/-- An injective duality map between finite modules of equal cardinality is a perfect pairing. -/
theorem isPerfPair_of_injective_of_natCard_eq [Finite N]
    (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hcard : Nat.card M = Nat.card N) : B.IsPerfPair := by
  apply (isPerfPair_iff_bijective n B).mpr
  apply (Nat.bijective_iff_injective_and_card B).mpr
  exact ⟨hB, hcard.trans (natCard_dual n N).symm⟩

/-- Nondegeneracy in both arguments of a finite ZMod pairing implies perfectness. -/
theorem isPerfPair_of_injective [Finite M] [Finite N]
    (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n)
    (hB : Function.Injective B) (hB' : Function.Injective B.flip) : B.IsPerfPair := by
  apply isPerfPair_of_injective_of_natCard_eq n B hB
  apply Nat.le_antisymm
  · simpa only [natCard_dual] using Nat.card_le_card_of_injective B hB
  · simpa only [natCard_dual] using Nat.card_le_card_of_injective B.flip hB'

/-- A perfect finite ZMod pairing identifies the cardinalities of its original two modules. -/
theorem natCard_eq_of_isPerfPair [Finite N]
    (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n) (hB : B.IsPerfPair) :
    Nat.card M = Nat.card N :=
  (Nat.card_eq_of_bijective B hB.bijective_left).trans (natCard_dual n N)

end ZMod
