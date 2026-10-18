/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PowerSeriesConstantClosure

/-! # Consumers of the literal constant closure over power series -/

@[expose] public noncomputable section

namespace AglibTest.PowerSeriesConstantClosure

open Polynomial IsLocalRing
open PowerSeries.ConstantClosure

variable {k : Type*} [Field k] [CharZero k] (p : MonicIrreducible k)

/-- The extension ring and its residue field are the actual integral closure and quotient. -/
theorem actual_constant_reduction (x : AdjoinRoot p.val) :
    algebraMap (Closure p) (TopField p) (constantMap p x) =
        AdjoinRoot.coefficientMap (L := LaurentSeries k) p.val x ∧
      residue (Closure p) (constantMap p x) = residueEquiv p x :=
  ⟨constantMap_apply p x, (residueEquiv_apply p x).symm⟩

/-- No extension DVR or unramifiedness hypothesis is supplied. -/
theorem actual_unramified_degree :
    Module.finrank k (ResidueField (Closure p)) = p.val.natDegree ∧
      Irreducible (algebraMap (PowerSeries k) (Closure p) PowerSeries.X) :=
  degree_and_uniformizer p

/-- The residue identification preserves the original base coefficients. -/
theorem actual_coefficient_square (a : k) :
    residueEquiv p (algebraMap k (AdjoinRoot p.val) a) =
      algebraMap (ResidueField (PowerSeries k)) (ResidueField (Closure p))
        (PowerSeries.residueFieldOfPowerSeries.symm a) :=
  residueEquiv_algebraMap p a

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`PowerSeries.ConstantClosure).isPrefixOf name ||
        (`AglibTest.PowerSeriesConstantClosure).isPrefixOf name then
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} constant-closure declarations: standard foundations only."

end AglibTest.PowerSeriesConstantClosure
