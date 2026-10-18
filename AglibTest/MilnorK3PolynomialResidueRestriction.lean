/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialResidueRestriction
public import Lean.Util.CollectAxioms

/-! # Original-group consumers of actual polynomial and infinity restriction -/

@[expose] public noncomputable section

namespace AglibTest.MilnorK3PolynomialResidueRestriction

open Polynomial Polynomial.LocalResidue
open MilnorK.K2 MilnorK.K3

variable {k L : Type*} [Field k] [Field L] (φ : k →+* L)

/-- The field map preserves the original variable and extends actual constants. -/
theorem actual_coefficient_map (a : k) :
    fractionMap φ (RatFunc.C a) = RatFunc.C (φ a) ∧
      fractionMap φ (RatFunc.X : RatFunc k) = RatFunc.X :=
  ⟨fractionMap_C φ a, fractionMap_X φ⟩

/-- Actual inversion commutes with coefficient extension on every rational function. -/
theorem actual_inversion_commutes (f : RatFunc k) :
    fractionMap φ (RatFunc.inversion k f) = RatFunc.inversion L (fractionMap φ f) :=
  fractionMap_inversion φ f

/-- A factor above an arbitrary original irreducible gives the actual K₃/K₂ square. -/
theorem original_finite_residue_commutes [CharZero k]
    (p : k[X]) (q : L[X]) [Fact (Irreducible p)] [Fact (Irreducible q)]
    (hq : q ∣ p.map φ) (x : MilnorK.K3.Group (RatFunc k)) :
    PolynomialResidue.residueAt q
        (MilnorK.K3.map (fractionMap φ) x) =
      MilnorK.K2.map (adjoinRootMap φ p q hq)
        (PolynomialResidue.residueAt p x) :=
  PolynomialResidue.residueAt_restrict φ p q hq x

/-- The square retains the literal local DVR residues and literal residue equivalences. -/
theorem original_dvr_residue_commutes [CharZero k]
    (p : k[X]) (q : L[X]) [Fact (Irreducible p)] [Fact (Irreducible q)]
    (hq : q ∣ p.map φ) (x : MilnorK.K3.Group (RatFunc k)) :
    MilnorK.K2.map (residueEquiv q).toRingHom
        (MilnorK.K3.DVR.residue (Ring q) (RatFunc L)
          (MilnorK.K3.map (fractionMap φ) x)) =
      MilnorK.K2.map (adjoinRootMap φ p q hq)
        (MilnorK.K2.map (residueEquiv p).toRingHom
          (MilnorK.K3.DVR.residue (Ring p) (RatFunc k) x)) :=
  PolynomialResidue.residueAt_restrict φ p q hq x

/-- At infinity the target map is the original Milnor K₂ restriction over the base fields. -/
theorem original_infinity_residue_commutes [CharZero k] (x : MilnorK.K3.Group (RatFunc k)) :
    InfinityResidue.residue L (MilnorK.K3.map (fractionMap φ) x) =
      MilnorK.K2.map φ (InfinityResidue.residue k x) :=
  InfinityResidue.residue_restrict φ x

open Lean in
run_cmd do
  for name in #[``Polynomial.LocalResidue.fractionMap_C,
      ``Polynomial.LocalResidue.fractionMap_X,
      ``Polynomial.LocalResidue.fractionMap_inversion,
      ``Polynomial.LocalResidue.fractionMap_comp_inversion,
      ``PolynomialResidue.residueAt_restrict,
      ``PolynomialResidue.residueAt_comp_restrict,
      ``InfinityResidue.rootXEquiv_adjoinRootMap,
      ``InfinityResidue.residue_restrict,
      ``InfinityResidue.residue_comp_restrict,
      ``actual_coefficient_map, ``actual_inversion_commutes,
      ``original_finite_residue_commutes, ``original_dvr_residue_commutes,
      ``original_infinity_residue_commutes] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite and infinity residue restriction uses only standard Lean logical foundations."

end AglibTest.MilnorK3PolynomialResidueRestriction
