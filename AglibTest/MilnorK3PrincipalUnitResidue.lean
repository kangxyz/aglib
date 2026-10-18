/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PrincipalUnitResidue
public import Lean.Util.CollectAxioms

/-! # Principal-unit residue consumers with arbitrary other entries -/

@[expose] public noncomputable section

open Polynomial MilnorK.K3

namespace AglibTest.MilnorK3PrincipalUnitResidue

variable {k : Type*} [Field k]

/-- The other two entries are unrestricted rational functions, rather than
assumed units in the local ring. -/
theorem actual_finite_place (p f g : k[X]) [Fact (Irreducible p)]
    (hf : f ≠ 0) (hg : g ≠ 0) (hpf : ¬ p ∣ f) (hpg : ¬ p ∣ g)
    (hfg : PolynomialResidue.quotientUnit p f hpf =
      PolynomialResidue.quotientUnit p g hpg) (a b : (RatFunc k)ˣ) :
    PolynomialResidue.residueAt p
      (symbol3 (PolynomialResidue.polynomialUnit f hf /
        PolynomialResidue.polynomialUnit g hg) a b) = 0 :=
  PolynomialResidue.residueAt_polynomial_ratio_eq_zero p f g hf hg hpf hpg hfg a b

/-- Equal-degree monic quotients have residue one at the actual infinity place,
and the other coordinates may have poles there. -/
theorem actual_infinity (f g : k[X]) (hf : f.Monic) (hg : g.Monic)
    (hd : f.natDegree = g.natDegree) (a b : (RatFunc k)ˣ) :
    InfinityResidue.residue k
      (symbol3 (PolynomialResidue.polynomialUnit f hf.ne_zero /
        PolynomialResidue.polynomialUnit g hg.ne_zero) a b) = 0 :=
  InfinityResidue.residue_monic_ratio f g hf hg hd a b

/-- Negative multiplicities vanish in the original residue target too. -/
theorem signed_infinity (f g : k[X]) (hf : f.Monic) (hg : g.Monic)
    (hd : f.natDegree = g.natDegree) (n : ℤ) (a b : (RatFunc k)ˣ) :
    InfinityResidue.residue k
      (n • symbol3 (PolynomialResidue.polynomialUnit f hf.ne_zero /
        PolynomialResidue.polynomialUnit g hg.ne_zero) a b) = 0 := by
  rw [map_zsmul, actual_infinity f g hf hg hd a b, smul_zero]

open Lean in
run_cmd do
  for name in #[``DVR.residue_principal_unit,
      ``PolynomialResidue.residueAt_polynomial_ratio_eq_zero,
      ``InfinityResidue.residue_monic_ratio, ``actual_finite_place,
      ``actual_infinity, ``signed_infinity] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Principal-unit finite and infinite residues use only standard foundations."

end AglibTest.MilnorK3PrincipalUnitResidue
