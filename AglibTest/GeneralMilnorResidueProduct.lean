/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.Residue.Product
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct legacy consumers of left local-unit projection. The right factor is
an arbitrary quotient class. Explicit poles, repeated minus-one factors, the
empty left factor, and actual DVR ring-unit reduction remain visible. -/

open MilnorK

namespace AglibTest.GeneralMilnorResidueProduct

universe u v

variable {L : Type u} {κ : Type v} [Field L] [Field κ]
variable (d : MilnorK.K2.DiscreteResidueData L κ) (hd : MilnorK.K2.UnitReductionCompatible d)

/-- Arbitrary positive degree on the right and arbitrary local-unit degree on
 the left, with the input degree transport explicit. -/
theorem arbitrary_right_class (m n : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) (z : K L (n + 1)) :
    residue d hd (m + n)
      (degreeCongr (Nat.add_assoc m n 1).symm (product m (n + 1) (symbol a) z)) =
      product m n (symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul))
        (residue d hd n z) :=
  residue_product_units_left_degreeCongr d hd m n a ha z

/-- The empty left symbol is included in every target degree. -/
theorem empty_left (n : ℕ) (z : K L (n + 1)) :
    residue d hd (0 + n)
      (degreeCongr (Nat.add_assoc 0 n 1).symm
        (product 0 (n + 1) (symbol Fin.elim0) z)) =
      product 0 n (symbol Fin.elim0) (residue d hd n z) := by
  have h := residue_product_units_left_degreeCongr d hd 0 n Fin.elim0
    (fun i => Fin.elim0 i) z
  have he : (fun i : Fin 0 => (d.unitPart (Additive.ofMul (Fin.elim0 i))).toMul) =
      Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rwa [he] at h

/-- In right degree one, an arbitrary signed valuation multiplies the literal
unit-part symbol, including the degree-zero source prefix. -/
theorem right_degree_one (m : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) (b : Lˣ) :
    residue d hd m (symbol (Fin.snoc a b)) =
      d.value (Additive.ofMul b) •
        symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul) := by
  rw [residue_symbol_snoc_units d hd m a ha b, specialize_symbol]

/-- Every repeated-uniformizer sign entry survives left multiplication. -/
theorem repeated_signs (m n : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) :
    residue d hd (m + n)
      (degreeCongr (Nat.add_assoc m n 1).symm
        (product m (n + 1) (symbol a) (symbol (fun _ => d.uniformizer)))) =
      product m n (symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul))
        (symbol (fun _ => (-1 : κˣ))) := by
  rw [residue_product_units_left_degreeCongr d hd m n a ha,
    residue_symbol_uniformizers]

/-- A negative-order last entry keeps the sign of the pole as well as every
repeated minus-one entry from the other uniformizers. -/
theorem negative_last_with_repeated_signs (m n : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) :
    residue d hd (m + n)
      (degreeCongr (Nat.add_assoc m n 1).symm
        (product m (n + 1) (symbol a)
          (symbol (Function.update (fun _ => d.uniformizer) (Fin.last n)
            d.uniformizer⁻¹)))) =
      -product m n (symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul))
        (symbol (fun _ => (-1 : κˣ))) := by
  rw [residue_product_units_left_degreeCongr d hd m n a ha,
    symbol_update_inv, Function.update_eq_self, map_neg,
    residue_symbol_uniformizers, map_neg]

/-- The two explicit poles on the right are allowed without valuation premises. -/
theorem mixed_poles (m : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) :
    residue d hd (m + 2)
      (degreeCongr (Nat.add_assoc m 2 1).symm
        (product m 3 (symbol a)
          (symbol ![d.uniformizer⁻¹, d.uniformizer ^ (-3 : ℤ), d.uniformizer]))) =
      product m 2 (symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul))
        (residue d hd 2
          (symbol ![d.uniformizer⁻¹, d.uniformizer ^ (-3 : ℤ), d.uniformizer])) :=
  residue_product_units_left_degreeCongr d hd m 2 a ha _

/-- Characteristic two is included; a repeated-uniformizer right factor of
positive residue degree vanishes by its actual minus-one coordinates. -/
theorem characteristic_two (d₂ : MilnorK.K2.DiscreteResidueData L (ZMod 2))
    (hd₂ : MilnorK.K2.UnitReductionCompatible d₂) (m n : ℕ) (a : SymbolTuple L m)
    (ha : ∀ i, d₂.value (Additive.ofMul (a i)) = 0) :
    residue d₂ hd₂ (m + (n + 1))
      (degreeCongr (Nat.add_assoc m (n + 1) 1).symm
        (product m (n + 1 + 1) (symbol a) (symbol (fun _ => d₂.uniformizer)))) = 0 := by
  rw [residue_product_units_left_degreeCongr d₂ hd₂ m (n + 1) a ha,
    residue_symbol_uniformizers]
  have h : symbol (fun _ : Fin (n + 1) => (-1 : (ZMod 2)ˣ)) = 0 := by
    apply symbol_eq_zero_of_eq_one _ 0
    apply Units.ext
    decide
  rw [h, map_zero]

section ActualDVR

variable (R L : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- Only genuine ring units occur on the left, and the target uses the literal
residue homomorphism of the actual DVR. -/
theorem literal_ring_unit_projection (m n : ℕ) (a : Fin m → Rˣ)
    (z : K L (n + 1)) :
    DVR.residue R L (m + n)
      (degreeCongr (Nat.add_assoc m n 1).symm
        (product m (n + 1) (symbol (MilnorK.K2.DVR.fieldUnits R L ∘ a)) z)) =
      product m n (symbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a))
        (DVR.residue R L n z) :=
  DVR.residue_product_ring_units_left R L m n a z

/-- Every class of a genuine base field acts through its map into the ring,
with no symbol restriction remaining on either quotient class. -/
theorem actual_base_field_projection {F : Type*} [Field F] (f : F →+* R)
    (m n : ℕ) (x : K F m) (z : K L (n + 1)) :
    DVR.residue R L (m + n)
      (degreeCongr (Nat.add_assoc m n 1).symm
        (product m (n + 1) (map m ((algebraMap R L).comp f) x) z)) =
      product m n (map m ((IsLocalRing.residue R).comp f) x) (DVR.residue R L n z) :=
  DVR.residue_product_base_field_left R L f m n x z

end ActualDVR

end AglibTest.GeneralMilnorResidueProduct

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
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorResidueProduct]
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
  logInfo m!"Checked {names.size} local-unit projection and general Milnor declarations: \
    standard axioms only."
