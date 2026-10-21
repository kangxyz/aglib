/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Valuation rings at all stalks of a Dedekind spectrum

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.DedekindValuation`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`,
SHA-256 `87d0bcb1ee780ce203e27eaaa2f2d2d26b7d0f125a91908036a33892be773b6a`, selected lines [[24,
37]].
The actual scheme objects, canonical maps, universes and conditions are retained.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- All stalks of the spectrum of a Dedekind domain are valuation rings,
including the generic field stalk. -/
theorem valuationRing_stalk_of_isDedekindDomain (A : Type u) [CommRing A] [IsDedekindDomain A]
    (x : Spec (CommRingCat.of A)) :
    ValuationRing ((Spec (CommRingCat.of A)).presheaf.stalk x) := by
  let : x.asIdeal.IsPrime := x.isPrime
  let R := (Spec (CommRingCat.of A)).presheaf.stalk x
  let : Algebra A R := StructureSheaf.stalkAlgebra A x
  let : IsLocalization.AtPrime R x.asIdeal := StructureSheaf.IsLocalization.to_stalk A x
  let : IsDedekindDomain R := IsLocalization.AtPrime.isDedekindDomain A x.asIdeal R
  by_cases h : IsField R
  · let := h.toField
    exact inferInstance
  · let : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R h).out 1 3).mpr
      (IsLocalization.AtPrime.isDedekindDomain A x.asIdeal R)
    exact inferInstance

end AlgebraicGeometry.Scheme
