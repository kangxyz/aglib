/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Compatibility
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct consumers for actual all-degree residue descent and full low-degree
compatibility. Principal entries are tested with arbitrary other entries and
with explicit poles; repeated uniformizers are tested without alternation. -/

open MilnorK

namespace AglibTest.GeneralMilnorResidue

universe u v

variable {L : Type u} {κ : Type v} [Field L] [Field κ]
variable (d : MilnorK.K2.DiscreteResidueData L κ) (hd : MilnorK.K2.UnitReductionCompatible d)

/-- A genuine map on the actual quotient exists in every positive source degree. -/
noncomputable def actual_residue (n : ℕ) : K L (n + 1) →ₗ[ℤ] K κ n := residue d hd n

/-- The entire recursion kills the multiplicativity relation at any coordinate. -/
theorem multilinear_descent (n : ℕ) (a : SymbolTuple L (n + 1))
    (i : Fin (n + 1)) (b c : Lˣ) :
    residueSymbol d hd n (Function.update a i (b * c)) =
      residueSymbol d hd n (Function.update a i b) +
        residueSymbol d hd n (Function.update a i c) := residueSymbol_mul d hd n a i b c

/-- All adjacent Steinberg relations vanish before passing to the quotient. -/
theorem steinberg_descent (n : ℕ) (a : SymbolTuple L (n + 1)) (i j : Fin (n + 1))
    (hij : i.val + 1 = j.val) (hab : (a i : L) + (a j : L) = 1) :
    residueSymbol d hd n a = 0 := residueSymbol_steinberg d hd n a i j hij hab

/-- The smallest residue is exactly the original signed integer order. -/
theorem degree_one (x : K L 1) :
    zeroEquiv κ (residue d hd 0 x) = d.value (oneEquiv L x) := zeroEquiv_residue d hd x

/-- Last-slot normalization includes the empty prefix and all higher degrees. -/
theorem last_uniformizer (n : ℕ) (a : SymbolTuple L n)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) :
    residue d hd n (symbol (Fin.snoc a d.uniformizer)) =
      symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul) :=
  residue_symbol_uniformizer d hd n a ha

/-- A pole in the last coordinate has the opposite normalized residue. -/
theorem inverse_uniformizer (n : ℕ) (a : SymbolTuple L n)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) :
    residue d hd n (symbol (Fin.snoc a d.uniformizer⁻¹)) =
      -symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul) := by
  have h := symbol_update_inv (Fin.snoc a d.uniformizer) (Fin.last n) d.uniformizer
  simp only [Fin.update_snoc_last] at h
  rw [h, map_neg, residue_symbol_uniformizer d hd n a ha]

/-- Principal-unit vanishing imposes no condition on any other entry's valuation. -/
theorem arbitrary_other_poles (n : ℕ) (a : SymbolTuple L (n + 1)) (i : Fin (n + 1))
    (hv : d.value (Additive.ofMul (a i)) = 0)
    (hu : d.unitPart (Additive.ofMul (a i)) = 0) : residue d hd n (symbol a) = 0 :=
  residue_symbol_principal d hd n a i hv hu

/-- A concrete fourth-degree symbol retains poles of orders one and three. -/
theorem explicit_poles (u : Lˣ) (hv : d.value (Additive.ofMul u) = 0)
    (hu : d.unitPart (Additive.ofMul u) = 0) :
    residue d hd 3 (symbol ![d.uniformizer⁻¹, u, d.uniformizer ^ (-3 : ℤ),
      d.uniformizer]) = 0 :=
  residue_symbol_principal d hd 3 _ 1 hv hu

/-- Repeated uniformizers produce all sign factors in every degree. -/
theorem repeated_uniformizers (n : ℕ) :
    residue d hd n (symbol (fun _ => d.uniformizer)) = symbol (fun _ => (-1 : κˣ)) :=
  residue_symbol_uniformizers d hd n

/-- Degree four specifically retains three target sign entries. -/
theorem degree_four_repeated :
    residue d hd 3 (symbol (fun _ => d.uniformizer)) =
      symbol (fun _ : Fin 3 => (-1 : κˣ)) := residue_symbol_uniformizers d hd 3

/-- The old tame map is matched on every degree-two class. -/
theorem old_tame (x : K L 2) :
    oneEquiv κ (residue d hd 1 x) = MilnorK.K2.tame d (twoEquiv L x) :=
  oneEquiv_residue_one d hd x

/-- The old degree-three residue is matched on every class, with no unit assumptions. -/
theorem old_residue_three (x : K L 3) :
    twoEquiv κ (residue d hd 2 x) = MilnorK.K3.residue3 d hd (threeEquiv L x) :=
  twoEquiv_residue_two d hd x

/-- In characteristic two the sign correction vanishes for its actual algebraic reason. -/
theorem repeated_uniformizers_characteristic_two
    (d₂ : MilnorK.K2.DiscreteResidueData L (ZMod 2))
    (hd₂ : MilnorK.K2.UnitReductionCompatible d₂) (n : ℕ) :
    residue d₂ hd₂ (n + 1) (symbol (fun _ => d₂.uniformizer)) = 0 := by
  rw [residue_symbol_uniformizers]
  apply symbol_eq_zero_of_eq_one _ 0
  apply Units.ext
  decide

end AglibTest.GeneralMilnorResidue

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
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorResidue]
  let selectedDeclaration (name : Name) := prefixes.any (·.isPrefixOf name)
  let selected (name : Name) : Bool :=
    libraryOrigin name || selectedDeclaration name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  for i in [:env.header.moduleNames.size] do
    if isLibraryModule env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} residue and general Milnor declarations: standard axioms only."
