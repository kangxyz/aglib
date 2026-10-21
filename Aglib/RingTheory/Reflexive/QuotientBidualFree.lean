/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Ext.QuotSMulTop
public import Aglib.Algebra.Category.ModuleCat.Ext.DualQuotient
public import Aglib.RingTheory.Reflexive.BidualPuncturedFree
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthDualComparison
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthExtComparison

/-!
# Lifting freeness from a scalar quotient's bidual

Finite-length defects of quotient evaluation suffice: evaluation need not be
injective. In quotient dimension at least three, the two actual finite-defect
comparisons give vanishing first Ext and a free dual. Change of rings and
coefficient Nakayama then give the original dual quotient and lift its freeness.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian

namespace Module

/-- Freeness of the quotient bidual lifts to a finite reflexive module, provided
its quotient is punctured-free and the regular quotient has dimension at least three. -/
theorem free_of_free_quotient_doubleDual
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsReflexive R M] (a : R)
    (ha : IsSMulRegular R a) (haM : IsSMulRegular M a)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {a})]
    (d : ℕ) (hd : ringKrullDim (R ⧸ Ideal.span {a}) = (d : ℕ)) (h3 : 3 ≤ d)
    (hfree : ∀ p : PrimeSpectrum (R ⧸ Ideal.span {a}),
      p.asIdeal ≠ IsLocalRing.maximalIdeal (R ⧸ Ideal.span {a}) →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (QuotSMulTop a M)))
    [Module.Free (R ⧸ Ideal.span {a})
      (Dual (R ⧸ Ideal.span {a}) (Dual (R ⧸ Ideal.span {a}) (QuotSMulTop a M)))] :
    Module.Free R M := by
  let Q := R ⧸ Ideal.span {a}
  let U := QuotSMulTop a M
  let N := Dual Q (Dual Q U)
  have : Module.Finite Q U := Module.Finite.of_restrictScalars_finite R Q U
  obtain ⟨hker, hcoker⟩ := isFiniteLength_eval_defects_of_free_punctured hfree
  let ee := IsRegularLocalRing.extOneLinearEquivOfIsFiniteLength Q
    (ModuleCat.ofHom (Dual.eval Q U)) hker hcoker d hd h3
  have : Subsingleton (Ext (ModuleCat.of Q N) (ModuleCat.of Q Q) 1) :=
    Ext.subsingleton_of_projective _ _ 0
  have : Subsingleton (Ext (ModuleCat.of Q U) (ModuleCat.of Q Q) 1) :=
    ee.symm.injective.subsingleton
  let ed := LinearEquiv.ofBijective (Dual.eval Q U).dualMap
    (IsRegularLocalRing.bijective_dualMap_of_isFiniteLength Q
      (Dual.eval Q U) hker hcoker d hd (by omega))
  have : Module.Free Q (Dual Q U) := Module.Free.of_equiv ed
  let eh := (QuotSMulTop.homLinearEquiv a M Q).extendScalarsOfSurjective
    (S := Q) Ideal.Quotient.mk_surjective
  have : Module.Free Q (M →ₗ[R] Q) := Module.Free.of_equiv eh
  obtain ⟨P, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R M
  let S := p.shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hp
  let ec := ModuleCat.extOneQuotSMulTopLinearEquiv a hS haM
  have : Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R Q) 1) :=
    ec.injective.subsingleton
  have : Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1) :=
    subsingleton_ext_one_of_quotient a ha ham
  have : Module.Free R (Dual R M) := free_dual_of_free_quotientHom a ha ham
  exact Module.Free.of_equiv (Module.evalEquiv R M).symm

end Module
