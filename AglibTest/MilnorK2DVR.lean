/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.K2.DVR.Uniformizer
import Lean.Util.CollectAxioms

/-!
# Concrete DVR consumers and rejecting axiom audit

These tests instantiate the original Milnor residue constructions from an actual
mathlib discrete valuation ring and its fraction field. The valuation, normalized
ring-unit lift, and actual residue ring homomorphism supply every elementary
residue-data and zero-valuation compatibility premise. Uniformizer changes use
the ring unit relating the two irreducibles, with no change formula assumed.
Legacy imports expose private helpers for the exhaustive implementation audit.
No Quillen comparison, finite-extension norm, or reciprocity assertion is made.
-/

open MilnorK.K2
open IsLocalRing

noncomputable section

namespace AglibTest.MilnorK2DVR

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The valuation is literally the maximal-ideal valuation on the fraction field. -/
theorem actual_valuation :
    DVR.valuation R K = (IsDiscreteValuationRing.maximalIdeal R).valuation K := rfl

/-- The integer order uses the original negative logarithm convention. -/
theorem actual_order (a : Kˣ) :
    DVR.value R K (Additive.ofMul a) = -WithZero.log (DVR.valuation R K (a : K)) := rfl

/-- An irreducible provides the full elementary residue record without extra data. -/
example {π : R} (hπ : Irreducible π) : DiscreteResidueData K (ResidueField R) :=
  DVR.data hπ

/-- Zero-order compatibility is proved from actual ring reduction. -/
theorem actual_reduction_compatible {π : R} (hπ : Irreducible π) :
    UnitReductionCompatible (DVR.data (K := K) hπ) := DVR.unitReductionCompatible hπ

/-- A DVR also supplies a compatible constructor without specifying an irreducible. -/
theorem chosen_reduction_compatible :
    UnitReductionCompatible (DVR.chosenData R K) := DVR.chosenData_unitReductionCompatible R K

/-- The lift realizes the normalized field element, rather than supplying a residue axiom. -/
theorem actual_normalized_lift {π : R} (hπ : Irreducible π) (a : Kˣ) :
    DVR.fieldUnits R K (DVR.normalizedLift hπ a) =
      a * DVR.uniformizer (K := K) hπ ^ (-DVR.value R K (Additive.ofMul a)) :=
  DVR.normalizedLift_spec hπ a

/-- The normalization has integer order zero. -/
theorem normalized_order_zero {π : R} (hπ : Irreducible π) (a : Kˣ) :
    DVR.value R K (Additive.ofMul (DVR.normalizedUnit hπ a)) = 0 :=
  DVR.value_normalizedUnit hπ a

/-- The chosen irreducible has value one and trivial normalized residue. -/
theorem uniformizer_normalization {π : R} (hπ : Irreducible π) :
    (DVR.data (K := K) hπ).value
        (Additive.ofMul (DVR.uniformizer (K := K) hπ)) = 1 ∧
      (DVR.data (K := K) hπ).unitPart
        (Additive.ofMul (DVR.uniformizer (K := K) hπ)) = 0 :=
  ⟨DVR.value_uniformizer hπ, DVR.unitPart_uniformizer hπ⟩

/-- Embedded DVR units have order zero. -/
theorem ring_unit_order_zero (u : Rˣ) :
    DVR.value R K (Additive.ofMul (DVR.fieldUnits R K u)) = 0 :=
  DVR.value_fieldUnits R K u

/-- Their unit parts are exactly their images under the actual residue homomorphism. -/
theorem actual_ring_unit_reduction {π : R} (hπ : Irreducible π) (u : Rˣ) :
    (DVR.data (K := K) hπ).unitPart (Additive.ofMul (DVR.fieldUnits R K u)) =
      Additive.ofMul (Units.map (residue R).toMonoidHom u) := by
  change Additive.ofMul (DVR.unitResidue hπ (DVR.fieldUnits R K u)) = _
  rw [DVR.unitResidue_fieldUnits]

/-- Two genuine ring units have zero tame residue. -/
theorem tame_ring_units {π : R} (hπ : Irreducible π) (u v : Rˣ) :
    tame (DVR.data (K := K) hπ) (symbol (DVR.fieldUnits R K u) (DVR.fieldUnits R K v)) =
      0 := tame_units _ _ _ (DVR.value_fieldUnits R K u) (DVR.value_fieldUnits R K v)

/-- The degree-two last-slot normalization returns actual unit reduction. -/
theorem tame_uniformizer_last {π : R} (hπ : Irreducible π) (u : Rˣ) :
    tame (DVR.data (K := K) hπ)
        (symbol (DVR.fieldUnits R K u) (DVR.uniformizer (K := K) hπ)) =
      Additive.ofMul (Units.map (residue R).toMonoidHom u) :=
  (tame_unit_uniformizer (DVR.data hπ) _ (DVR.value_fieldUnits R K u)).trans
    (actual_ring_unit_reduction hπ u)

/-- First-slot normalization has the opposite additive sign. -/
theorem tame_uniformizer_first {π : R} (hπ : Irreducible π) (u : Rˣ) :
    tame (DVR.data (K := K) hπ)
        (symbol (DVR.uniformizer (K := K) hπ) (DVR.fieldUnits R K u)) =
      -Additive.ofMul (Units.map (residue R).toMonoidHom u) :=
  (tame_uniformizer_unit (DVR.data hπ) _ (DVR.value_fieldUnits R K u)).trans
    (congrArg Neg.neg (actual_ring_unit_reduction hπ u))

/-- A repeated uniformizer retains the actual residue of minus one. -/
theorem tame_uniformizer_diagonal {π : R} (hπ : Irreducible π) :
    tame (DVR.data (K := K) hπ)
        (symbol (DVR.uniformizer (K := K) hπ) (DVR.uniformizer (K := K) hπ)) =
      residueSign (ResidueField R) := by
  simp [tame_symbol, rawTame, DVR.data]

/-- Specialization of ring-unit symbols is the symbol of their actual reductions. -/
theorem specialization_ring_units {π : R} (hπ : Irreducible π) (u v : Rˣ) :
    specialize (DVR.data (K := K) hπ) (DVR.unitReductionCompatible hπ)
        (symbol (DVR.fieldUnits R K u) (DVR.fieldUnits R K v)) =
      symbol (Units.map (residue R).toMonoidHom u) (Units.map (residue R).toMonoidHom v) := by
  rw [specialize_symbol, actual_ring_unit_reduction hπ u, actual_ring_unit_reduction hπ v]
  rfl

/-- The concrete ratio is a ring unit satisfying the literal uniformizer equation. -/
theorem actual_uniformizer_ratio {π π' : R} (hπ : Irreducible π) (hπ' : Irreducible π') :
    π' = (DVR.uniformizerRatio hπ hπ' : R) * π := DVR.uniformizerRatio_spec hπ hπ'

/-- The unit-part correction is derived for the actual chosen ring unit. -/
theorem actual_unit_part_change {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') (a : UnitsAdd K) :
    (DVR.data (K := K) hπ').unitPart a = (DVR.data (K := K) hπ).unitPart a -
      (DVR.data (K := K) hπ).value a • DVR.uniformizerChange hπ hπ' :=
  DVR.unitPart_change hπ hπ' a

/-- Actual DVR tame maps are independent of the chosen irreducible. -/
theorem actual_tame_independence {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    tame (DVR.data (K := K) hπ') = tame (DVR.data (K := K) hπ) :=
  DVR.tame_uniformizer_independent hπ hπ'

/-- The literal full-group specialization correction has the original sign. -/
theorem actual_specialization_correction {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    specialize (DVR.data (K := K) hπ') (DVR.unitReductionCompatible hπ') =
      specialize (DVR.data (K := K) hπ) (DVR.unitReductionCompatible hπ) -
        (residueCorrection (DVR.uniformizerChange hπ hπ')).comp
          (tame (DVR.data (K := K) hπ)) :=
  DVR.specialize_uniformizer_change hπ hπ'

/-- The actual specialization is independent of the irreducible on the tame kernel. -/
theorem actual_unramified_independence {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') (x : MilnorK.K2.Group K)
    (hx : tame (DVR.data (K := K) hπ) x = 0) :
    specialize (DVR.data (K := K) hπ') (DVR.unitReductionCompatible hπ') x =
      specialize (DVR.data (K := K) hπ) (DVR.unitReductionCompatible hπ) x :=
  DVR.specialize_uniformizer_independent hπ hπ' x hx

end AglibTest.MilnorK2DVR

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName)
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The concrete DVR audit requires legacy imports to include private helpers"
  let libraryPrefix := `MilnorK.K2
  let consumerPrefix := `AglibTest.MilnorK2DVR
  let selectedDeclaration (name : Name) : Bool :=
    let libraryOrigin := match env.getModuleIdxFor? name with
      | some index => isLibraryModule env.header.moduleNames[index.toNat]!
      | none => false
    libraryOrigin || libraryPrefix.isPrefixOf name || consumerPrefix.isPrefixOf name
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    let libraryOrigin := isLibraryModule env.header.moduleNames[i]!
    for name in env.header.moduleData[i]!.constNames do
      if libraryOrigin || libraryPrefix.isPrefixOf name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError "Concrete DVR audit declaration {name} is missing from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} original Milnor K₂, concrete DVR, and consumer declarations, \
    including private helpers: only standard Lean logical foundations."
