/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.KTheory.MilnorK.StageLift
import Aglib.KTheory.MilnorK.LowDegree
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Direct consumers for the actual all-degree lower-stage section. The tests
retain the last-slot convention, empty tuples, arbitrary coordinate products,
literal polynomial representatives, and characteristic two. -/

open Polynomial MilnorK MilnorK.DegreeFiltration

namespace AglibTest.GeneralMilnorStageLift

universe u

variable {F : Type u} [Field F] (p : F[X]) [Fact (Irreducible p)]
variable (hp : p.Monic) (n : ℕ)

/-- The lift is a linear map between the original actual quotients. -/
noncomputable def actualLift :
    K (AdjoinRoot p) n →ₗ[ℤ] K (RatFunc F) (n + 1) ⧸ lower F (n + 1) p.natDegree :=
  stageLift p hp n

/-- Every residue-field class, not only a generator, is recovered by the actual residue. -/
theorem actual_section (x : K (AdjoinRoot p) n) :
    stageResidue p hp n (stageLift p hp n x) = x := stageResidue_stageLift p hp n x

/-- The section identity yields injectivity without any canonical-presentation hypothesis. -/
theorem actual_injective : Function.Injective (stageLift p hp n) := stageLift_injective p hp n

/-- Every coordinate has a proved multiplication law modulo the actual lower span. -/
theorem coordinate_product (a : SymbolTuple (AdjoinRoot p) n) (i : Fin n)
    (b c : (AdjoinRoot p)ˣ) :
    stageSymbol p hp (Function.update a i (b * c)) =
      stageSymbol p hp (Function.update a i b) + stageSymbol p hp (Function.update a i c) :=
  stageSymbol_mul p hp a i b c

/-- Each representative is bounded individually. -/
theorem individual_degree_bound (a : SymbolTuple (AdjoinRoot p) n) (i : Fin n) :
    (reducedRepresentative p hp (a i)).natDegree < p.natDegree :=
  reducedRepresentative_natDegree_lt p hp (a i)

/-- Already reduced polynomial entries retain their exact order and final uniformizer. -/
theorem literal_reduced_symbol (a : Fin n → F[X]) (ha : ∀ i, a i ≠ 0)
    (hdeg : ∀ i, (a i).natDegree < p.natDegree) :
    stageLift p hp n (symbol (fun i => PolynomialResidue.quotientUnit p (a i)
      (hp.not_dvd_of_natDegree_lt (ha i) (hdeg i)))) =
      (lower F (n + 1) p.natDegree).mkQ
        (symbol (Fin.snoc (polynomialTuple a ha)
          (polynomialUnit F p (Fact.out : Irreducible p).ne_zero))) :=
  stageLift_reduced p hp a ha hdeg

/-- Repeating a reduced entry requires no bound on the sum of its three degrees. -/
theorem repeated_reduced_entries (a : F[X]) (ha : a ≠ 0)
    (hdeg : a.natDegree < p.natDegree) :
    stageLift p hp 3 (symbol (fun _ : Fin 3 => PolynomialResidue.quotientUnit p a
      (hp.not_dvd_of_natDegree_lt ha hdeg))) =
      (lower F 4 p.natDegree).mkQ
        (symbol (Fin.snoc (fun _ : Fin 3 => polynomialUnit F a ha)
          (polynomialUnit F p (Fact.out : Irreducible p).ne_zero))) :=
  stageLift_reduced p hp (fun _ : Fin 3 => a) (fun _ => ha) (fun _ => hdeg)

/-- The smallest source degree lifts the empty symbol to the singleton polynomial symbol. -/
theorem empty_tuple :
    stageLift p hp 0 (symbol (Fin.elim0 : SymbolTuple (AdjoinRoot p) 0)) =
      (lower F 1 p.natDegree).mkQ
        (symbol (fun _ : Fin 1 => polynomialUnit F p (Fact.out : Irreducible p).ne_zero)) :=
  stageLift_empty p hp Fin.elim0

/-- Under the canonical degree-zero equivalence, this section has residue exactly one. -/
theorem empty_tuple_residue :
    zeroEquiv (AdjoinRoot p)
      (stageResidue p hp 0 (stageLift p hp 0 (symbol Fin.elim0))) = 1 := by
  rw [stageResidue_stageLift, zeroEquiv_symbol]

/-- Positive-degree adjacent Steinberg relations need no quotient correction. -/
theorem literal_steinberg (a : SymbolTuple (AdjoinRoot p) n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hab : (a i : AdjoinRoot p) + (a j : AdjoinRoot p) = 1) :
    symbol (Fin.snoc (reducedTuple p hp a)
      (polynomialUnit F p (Fact.out : Irreducible p).ne_zero)) = 0 :=
  reducedTuple_steinberg p hp a i j hij hab

/-- The actual section is also valid in characteristic two, with no sign division. -/
theorem characteristic_two_section (q : (ZMod 2)[X]) [Fact (Irreducible q)]
    (hq : q.Monic) (x : K (AdjoinRoot q) n) :
    stageResidue q hq n (stageLift q hq n x) = x := stageResidue_stageLift q hq n x

end AglibTest.GeneralMilnorStageLift

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.PolynomialLocalResidue]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`MilnorK, `AglibTest.GeneralMilnorStageLift]
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
  logInfo m!"Checked {names.size} general Milnor and stage-lift declarations: standard axioms only."
