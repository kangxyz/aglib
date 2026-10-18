/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialLocalResidue
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual polynomial local ring

These tests expose the concrete localization at `(p)`, its actual residue field,
and `RatFunc k`. They check polynomial/scalar reduction, rational-function
inclusion, uniformizers, and units of reduced degree over an arbitrary field.
-/

@[expose] public noncomputable section

open Polynomial

namespace AglibTest.PolynomialLocalResidue

universe u

variable {k : Type u} [Field k] (p : k[X]) [Fact (Irreducible p)]

/-- The ring under test is the actual prime localization. -/
theorem actual_local_ring_is_dvr :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {p})) :=
  inferInstanceAs (IsDiscreteValuationRing (LocalResidue.Ring p))

/-- The fraction field is the actual rational-function field. -/
theorem actual_fraction_field :
    IsFractionRing (Localization.AtPrime (Ideal.span {p})) (RatFunc k) :=
  inferInstanceAs (IsFractionRing (LocalResidue.Ring p) (RatFunc k))

/-- The localization inclusion preserves the original polynomial map to rational functions. -/
theorem rational_function_polynomial (q : k[X]) :
    algebraMap (Localization.AtPrime (Ideal.span {p})) (RatFunc k)
      (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) q) =
        algebraMap k[X] (RatFunc k) q :=
  (IsScalarTower.algebraMap_apply k[X] (LocalResidue.Ring p) (RatFunc k) q).symm

/-- The inverse residue equivalence sends the actual reduced polynomial to its quotient class. -/
theorem actual_polynomial_reduction (q : k[X]) :
    LocalResidue.residueEquiv p
      (IsLocalRing.residue (Localization.AtPrime (Ideal.span {p}))
        (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) q)) =
      AdjoinRoot.mk p q :=
  LocalResidue.residueEquiv_residue_polynomial p q

/-- Constants retain their actual `k`-algebra structure. -/
theorem actual_scalar_reduction (a : k) :
    LocalResidue.residueEquiv p
      (IsLocalRing.residue (Localization.AtPrime (Ideal.span {p}))
        (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) (C a))) =
      algebraMap k (AdjoinRoot p) a := by
  rw [actual_polynomial_reduction, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

/-- The polynomial coordinate reduces to the original adjoined root. -/
theorem actual_coordinate_reduction :
    LocalResidue.residueEquiv p
      (IsLocalRing.residue (Localization.AtPrime (Ideal.span {p}))
        (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) X)) =
      AdjoinRoot.root p := by
  rw [actual_polynomial_reduction, AdjoinRoot.mk_X]

/-- The defining polynomial is killed by reduction. -/
theorem actual_defining_polynomial_reduction :
    LocalResidue.residueEquiv p
      (IsLocalRing.residue (Localization.AtPrime (Ideal.span {p}))
        (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) p)) = 0 := by
  rw [actual_polynomial_reduction, AdjoinRoot.mk_self]

/-- The uniformizer is precisely the localized defining polynomial. -/
theorem actual_uniformizer :
    Irreducible (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) p) :=
  LocalResidue.irreducible_polynomial p

/-- Any nonzero polynomial of smaller degree than a monic `p` is an actual local unit. -/
theorem actual_reduced_polynomial_unit (hp : p.Monic) (q : k[X]) (hq : q ≠ 0)
    (hdeg : q.natDegree < p.natDegree) :
    IsUnit (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) q) :=
  LocalResidue.isUnit_polynomial_of_natDegree_lt p hp hq hdeg

/-- The same reduced representative has nonzero residue, without separability assumptions. -/
theorem actual_reduced_polynomial_residue_nonzero (hp : p.Monic) (q : k[X]) (hq : q ≠ 0)
    (hdeg : q.natDegree < p.natDegree) :
    IsLocalRing.residue (Localization.AtPrime (Ideal.span {p}))
      (algebraMap k[X] (Localization.AtPrime (Ideal.span {p})) q) ≠ 0 := by
  intro h
  have he := actual_polynomial_reduction p q
  rw [h, map_zero] at he
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt hp hq hdeg he.symm

open Lean in
run_cmd do
  for name in #[``LocalResidue.primeIdeal_ne_bot,
      ``LocalResidue.instIsDiscreteValuationRing, ``LocalResidue.instAlgebraRatFunc,
      ``LocalResidue.instIsScalarTowerRatFunc, ``LocalResidue.instIsFractionRingRatFunc,
      ``LocalResidue.adjoinRootEquiv, ``LocalResidue.residueEquiv,
      ``LocalResidue.adjoinRootEquiv_mk, ``LocalResidue.residueEquiv_algebraMap,
      ``LocalResidue.residueEquiv_residue_polynomial, ``LocalResidue.residueEquiv_residue_eq_aeval,
      ``LocalResidue.maximalIdeal_eq_span, ``LocalResidue.irreducible_polynomial,
      ``LocalResidue.isUnit_polynomial_iff, ``LocalResidue.isUnit_polynomial_of_natDegree_lt,
      ``actual_local_ring_is_dvr, ``actual_fraction_field, ``rational_function_polynomial,
      ``actual_polynomial_reduction, ``actual_scalar_reduction, ``actual_coordinate_reduction,
      ``actual_defining_polynomial_reduction, ``actual_uniformizer,
      ``actual_reduced_polynomial_unit, ``actual_reduced_polynomial_residue_nonzero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Polynomial local residue audit passed: standard foundations only."

end AglibTest.PolynomialLocalResidue
