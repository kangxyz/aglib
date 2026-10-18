/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DVRNormValuation
public import Aglib.KTheory.MilnorK.K2.DVR.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of the ordinary DVR norm valuation theorem

The inputs are actual compatible fraction fields and the actual integral
closure. The residue degree is the finrank of the literal residue-field map.
Both arbitrary units and poles are covered. The Milnor-order adapter is only
in this consumer, so the general ring-theory implementation has no K-theory
import.
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing.NormValuation

namespace AglibTest.DVRNormValuation

variable (R B K L : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra R B] [Module.Finite R B] [Module.IsTorsionFree R B]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsScalarTower R B L] [IsFractionRing B L]
  [IsIntegralClosure B R L] [FiniteDimensional K L] [PerfectField K]

/-- Arbitrary nonzero field elements, without a compatibility premise. -/
theorem arbitrary_field_norm (h : Lˣ) :
    order R K (Units.map (Algebra.norm K) h) =
      (Module.finrank (ResidueField R) (ResidueField B) : ℤ) * order B L h :=
  order_norm R B K L h

/-- A genuine pole is included, with its negative integer order. -/
theorem inverse_uniformizer_norm {π : B} (hπ : Irreducible π) :
    order R K (Units.map (Algebra.norm K) (uniformizerUnit B L hπ)⁻¹) =
      -(Module.finrank (ResidueField R) (ResidueField B) : ℤ) := by
  rw [order_norm R B K L, order_inv, order_uniformizer, mul_neg, mul_one]

omit [PerfectField K] in
/-- The general native integer order is definitionally the order used by the
existing tame-symbol implementation. -/
theorem milnor_order_agrees (h : Kˣ) :
    MilnorK.K2.DVR.value R K (Additive.ofMul h) = order R K h := rfl

/-- The ordinary field norm therefore has the exact downstream Milnor-order
statement, using the actual residue-field degree. -/
theorem actual_milnor_norm_order (h : Lˣ) :
    MilnorK.K2.DVR.value R K
        (Additive.ofMul (Units.map (Algebra.norm K) h)) =
      (Module.finrank (ResidueField R) (ResidueField B) : ℤ) *
        MilnorK.K2.DVR.value B L (Additive.ofMul h) :=
  order_norm R B K L h

end AglibTest.DVRNormValuation

open Lean in
run_cmd do
  for name in #[
      `IsDiscreteValuationRing.NormValuation.order,
      `IsDiscreteValuationRing.NormValuation.orderHom,
      `IsDiscreteValuationRing.NormValuation.order_mul,
      `IsDiscreteValuationRing.NormValuation.order_zpow,
      `IsDiscreteValuationRing.NormValuation.order_inv,
      `IsDiscreteValuationRing.NormValuation.order_ringUnit,
      `IsDiscreteValuationRing.NormValuation.order_uniformizer,
      `IsDiscreteValuationRing.NormValuation.norm_ringUnit,
      `IsDiscreteValuationRing.NormValuation.order_norm_ringUnit,
      `IsDiscreteValuationRing.NormValuation.span_intNorm_uniformizer,
      `IsDiscreteValuationRing.NormValuation.order_norm_uniformizer,
      `IsDiscreteValuationRing.NormValuation.order_norm,
      `AglibTest.DVRNormValuation.arbitrary_field_norm,
      `AglibTest.DVRNormValuation.inverse_uniformizer_norm,
      `AglibTest.DVRNormValuation.milnor_order_agrees,
      `AglibTest.DVRNormValuation.actual_milnor_norm_order] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Ordinary DVR norm orders and poles use only standard Lean foundations."
