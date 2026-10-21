/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint
public import Aglib.AlgebraicGeometry.Blowup.RegularAway
public import Aglib.RingTheory.RegularLocalRing.PrimeLocalization
public import Aglib.RingTheory.RegularLocalRing.QuotientLift

/-!
# Regularity of the actual regular-local point blowup

The same ordered parameters as the actual exceptional-projective-line
comparison give the actual quotient charts. On the exceptional fibre their
local rings are regular by lifting through the original regular equation.
The original blowdown comparison gives regularity off the centre.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Polynomial
open Localization.Away

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

variable {A : Type u} [CommRing A]

private theorem pairQuotient_isRegularRing_quotient (a b : A)
    [IsRegularRing (A ⧸ Ideal.span {a, b})] :
    IsRegularRing (pairQuotient a b ⧸
      Ideal.span {algebraMap A (pairQuotient a b) a}) := by
  have hJ : (Ideal.span {a, b}).map (algebraMap A (pairQuotient a b)) =
      Ideal.span {algebraMap A (pairQuotient a b) a} := by
    rw [Ideal.map_span, Set.image_pair]
    exact Ideal.span_pair_eq_span_left_iff_dvd.mpr
      ⟨pairCoordinate a b, (pairCoordinate_relation a b).symm⟩
  have hreg : IsRegularRing (pairFibre a b) :=
    IsRegularRing.of_ringEquiv (pairFibreEquiv a b).symm.toRingEquiv
  change IsRegularRing (pairQuotient a b ⧸
    (Ideal.span {a, b}).map (algebraMap A (pairQuotient a b))) at hreg
  rwa [hJ] at hreg

/-- The actual blowup stalk at a point of an original polynomial fibre chart
is regular. Quotient regularity is supplied for the original coefficient quotient. -/
theorem regularLocalRing_chartFibreToBlowup [IsNoetherianRing A]
    (I : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    [IsRegularRing (A ⧸ I)] (p : Spec (.of (A ⧸ I)[X])) :
    IsRegularLocalRing ((canonicalBlowup I).presheaf.stalk
      (chartFibreToBlowup I a b hI ha hb p)) := by
  let Q := pairQuotient a b
  let r := rawChartReduction I a b hI ha hb
  let f : Spec (.of (A ⧸ I)[X]) ⟶ Spec (.of Q) :=
    Spec.map (CommRingCat.ofHom r.toRingHom)
  let y : Spec (.of Q) := f p
  have haI : a ∈ I := hI ▸ Ideal.subset_span (by simp)
  have hzero : r (algebraMap A Q a) = 0 := by
    rw [r.commutes]
    change C (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr haI, map_zero]
  have hy : algebraMap A Q a ∈ y.asIdeal := by
    change r (algebraMap A Q a) ∈ p.asIdeal
    rw [hzero]
    exact p.asIdeal.zero_mem
  let : IsRegularRing (A ⧸ Ideal.span {a, b}) := by rw [hI]; infer_instance
  let : IsRegularRing (Q ⧸ Ideal.span {algebraMap A Q a}) :=
    pairQuotient_isRegularRing_quotient a b
  have haQ : IsSMulRegular Q (algebraMap A Q a) := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro q hq
    apply pairQuotient_smulRegular a b ha hb
    simpa only [Algebra.smul_def, smul_eq_mul, mul_zero, Algebra.algebraMap_self_apply] using hq
  let : y.asIdeal.IsPrime := y.2
  let : IsRegularLocalRing (Localization.AtPrime y.asIdeal) :=
    IsRegularLocalRing.atPrime_of_quotient_span_singleton Q (algebraMap A Q a) haQ y.asIdeal hy
  let : IsRegularLocalRing ((Spec (.of Q)).presheaf.stalk y) :=
    IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (.of Q) y).commRingCatIsoToRingEquiv.symm
  have hstalk : IsRegularLocalRing ((canonicalBlowup I).presheaf.stalk
      (rawChart I a b hI ha hb y)) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso ((rawChart I a b hI ha hb).stalkMap y)).commRingCatIsoToRingEquiv.symm
  have he : rawChart I a b hI ha hb y = chartFibreToBlowup I a b hI ha hb p := by
    exact congrArg (fun g : Spec (.of (A ⧸ I)[X]) ⟶ canonicalBlowup I => g p)
      (rawChartReduction_chart I a b hI ha hb)
  exact he ▸ hstalk

/-- The original regular-pair fibre charts prove regularity at every point of
the actual exceptional fibre inside the constructed blowup. -/
theorem regularLocalRing_exceptionalι [IsNoetherianRing A]
    (I : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
    (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)
    [IsRegularRing (A ⧸ I)] (e : exceptionalFibre I) :
    IsRegularLocalRing ((canonicalBlowup I).presheaf.stalk (exceptionalι I e)) := by
  rcases fibreCharts_cover I a b hI ha hb hb' ha' e with h | h
  · obtain ⟨p, rfl⟩ := h
    have he := congrArg (fun g : Spec (.of (A ⧸ I)[X]) ⟶ canonicalBlowup I => g p)
      (fibreChart_fst I a b hI ha hb)
    change exceptionalι I (fibreChart I a b hI ha hb p) = _ at he
    rw [he]
    exact regularLocalRing_chartFibreToBlowup I a b hI ha hb p
  · obtain ⟨p, rfl⟩ := h
    have he := congrArg (fun g : Spec (.of (A ⧸ I)[X]) ⟶ canonicalBlowup I => g p)
      (fibreChart_fst I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    change exceptionalι I (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha' p) = _ at he
    rw [he]
    exact regularLocalRing_chartFibreToBlowup I b a (Ideal.span_pair_comm.trans hI) hb' ha' p

/-- Blowing up the actual maximal ideal of a two-dimensional regular local ring
has regular actual stalks, with no additional hypotheses on the local ring. -/
@[stacks 0AGR]
theorem regularStalks (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hd : ringKrullDim A = 2) :
    Scheme.RegularStalks (blowupDatum (affineCenter A (maximalIdeal A))).Y := by
  let I := maximalIdeal A
  let a := firstParameter A hd
  let b := secondParameter A hd
  have h := parameters_spec A hd
  let : IsRegularRing A := IsRegularLocalRing.isRegularRing_of_regularLocal A
  let : IsRegularRing (A ⧸ I) := inferInstanceAs (IsRegularRing (ResidueField A))
  intro z
  by_cases hz : blowdown I z ∈ Set.range (quotientImmersion I)
  · have hz' : z ∈ Set.range (exceptionalι I) := by
      change z ∈ Set.range (pullback.fst (blowdown I) (quotientImmersion I))
      rw [Scheme.Pullback.range_fst]
      exact hz
    obtain ⟨e, rfl⟩ := hz'
    exact regularLocalRing_exceptionalι I a b h.2.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 e
  · exact blowup_regular_away (quotientImmersion I)
      (blowupDatum (affineCenter A I)) (fun y _ => Scheme.regularStalks_spec A y) z hz

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
