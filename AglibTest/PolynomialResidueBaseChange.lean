/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.RingTheory.PolynomialResidueBaseChange
import Lean.Util.CollectAxioms

/-!
# Actual polynomial-place scalar base-change consumers

These statements retain the original polynomial quotients, prime localizations,
residue fields, and rational-function fields. In characteristic zero the
transported source polynomial generates the target maximal ideal. The rejecting
axiom audit includes the complete library modules and these consumers.
-/

noncomputable section

open Polynomial
open Polynomial.LocalResidue

namespace AglibTest.PolynomialResidueBaseChange

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L]
variable (φ : k →+* L) (p : k[X]) (q : L[X])
variable [Fact (Irreducible p)] [Fact (Irreducible q)] (hq : q ∣ p.map φ)

include hq in
/-- The prime contraction is an equality of the original principal ideals. -/
theorem actual_prime_contraction :
    Ideal.span {p} = (Ideal.span {q}).comap (Polynomial.mapRingHom φ) :=
  primeIdeal_eq_comap φ p q hq

/-- The actual localizations admit the required local homomorphism. -/
def actual_local_map :
    Localization.AtPrime (Ideal.span {p}) →+* Localization.AtPrime (Ideal.span {q}) :=
  localRingMap φ p q hq

/-- The map has the localness property used to construct the actual residue map. -/
theorem actual_local_map_isLocalHom : IsLocalHom (actual_local_map φ p q hq) :=
  inferInstanceAs (IsLocalHom (localRingMap φ p q hq))

/-- Polynomial classes map by literal coefficient extension. -/
theorem actual_quotient_polynomial (a : k[X]) :
    adjoinRootMap φ p q hq (AdjoinRoot.mk p a) = AdjoinRoot.mk q (a.map φ) :=
  adjoinRootMap_mk φ p q hq a

/-- The quotient map sends the original root to the new root. -/
theorem actual_root_image :
    adjoinRootMap φ p q hq (AdjoinRoot.root p) = AdjoinRoot.root q :=
  adjoinRootMap_root φ p q hq

/-- The quotient map restricts to the specified map of coefficient fields. -/
theorem actual_coefficient_image (a : k) :
    adjoinRootMap φ p q hq (algebraMap k (AdjoinRoot p) a) =
      algebraMap L (AdjoinRoot q) (φ a) :=
  adjoinRootMap_algebraMap φ p q hq a

/-- The residue-field square uses the residue map of the constructed local map. -/
theorem actual_residue_square
    (a : IsLocalRing.ResidueField (Localization.AtPrime (Ideal.span {p}))) :
    residueEquiv q (IsLocalRing.ResidueField.map (localRingMap φ p q hq) a) =
      adjoinRootMap φ p q hq (residueEquiv p a) :=
  residueEquiv_residueMap φ p q hq a

/-- Fraction-field compatibility holds on every element of the original local ring. -/
theorem actual_fraction_square (a : Localization.AtPrime (Ideal.span {p})) :
    fractionMap φ
      (algebraMap (Localization.AtPrime (Ideal.span {p})) (RatFunc k) a) =
      algebraMap (Localization.AtPrime (Ideal.span {q})) (RatFunc L)
        (localRingMap φ p q hq a) :=
  fractionMap_algebraMap_localRing φ p q hq a

/-- Squarefreeness is a consequence of characteristic zero, rather than an input. -/
theorem actual_squarefree [CharZero k] : Squarefree (p.map φ) :=
  squarefree_map φ p

include hq in
/-- The factor complementary to the chosen target place is prime to that place. -/
theorem actual_factor [CharZero k] : ∃ h : L[X], p.map φ = q * h ∧ ¬q ∣ h :=
  exists_factor_not_dvd φ p q hq

/-- The transported defining polynomial is an actual irreducible of the target DVR. -/
theorem actual_transported_uniformizer [CharZero k] :
    Irreducible (localRingMap φ p q hq
      (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) p)) :=
  irreducible_localRingMap_polynomial φ p q hq

/-- The transported source polynomial generates the target maximal ideal. -/
theorem actual_maximalIdeal [CharZero k] :
    IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {q})) =
      Ideal.span {localRingMap φ p q hq
        (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) p)} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
    (irreducible_localRingMap_polynomial φ p q hq)

end AglibTest.PolynomialResidueBaseChange

open Lean in
run_cmd do
  let env ← getEnv
  let libraryModulePrefixes := #[`Aglib.KTheory.MilnorK]
  let libraryHelperModules := #[
    `Aglib.RingTheory.PolynomialLocalResidue,
    `Aglib.RingTheory.PolynomialResidueBaseChange]
  let isLibraryModule (moduleName : Name) : Bool :=
    libraryModulePrefixes.any (·.isPrefixOf moduleName) ||
      libraryHelperModules.contains moduleName
  let libraryOrigin (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some index => isLibraryModule env.header.moduleNames[index.toNat]!
    | none => false
  if env.header.isModule then
    throwError "The polynomial base-change audit requires legacy imports for private helpers"
  let libraryPrefixes := #[`Motivic.Aglib.RingTheory.PolynomialLocalResidue,
    `Motivic.Aglib.RingTheory.PolynomialResidueBaseChange, `Polynomial.LocalResidue]
  let consumerPrefix := `AglibTest.PolynomialResidueBaseChange
  let isLibrary (name : Name) : Bool := libraryPrefixes.any (·.isPrefixOf name)
  let selectedDeclaration (name : Name) : Bool :=
    let libraryOrigin := match env.getModuleIdxFor? name with
      | some index => isLibraryModule env.header.moduleNames[index.toNat]!
      | none => false
    libraryOrigin || isLibrary name || consumerPrefix.isPrefixOf name
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
      if libraryOrigin || isLibrary name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      unless (env.checked.get.find? name).isSome do
        throwError "Polynomial base-change declaration {name} is absent from the kernel environment"
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} polynomial local residue, concrete scalar base-change, and consumer \
    declarations, including private helpers: only standard Lean logical foundations."
