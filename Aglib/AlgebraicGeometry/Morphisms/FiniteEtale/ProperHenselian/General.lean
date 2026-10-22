/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian.ApproximationSystem
public import Aglib.AlgebraicGeometry.Approximation.Proper.FiniteType

/-!
# Finite-etale covers over a proper henselian local base

The literal original closed-fibre restriction is an equivalence for every
proper scheme over every henselian local ring. Actual fixed-base proper FP
approximation, stage cover lifting and the existing graph construction supply
the comparison. No Noetherian, finite-presentation, flatness, excellence or
projectivity hypothesis is imposed at this endpoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

/-- Every original closed-fibre finite-etale cover lifts over an arbitrary
henselian local ring, without a finite-presentation assumption on the proper morphism. -/
theorem properHenselian_baseChange_essSurj :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).EssSurj := by
  obtain ⟨M⟩ := Scheme.Approximation.nonempty_properFinitePresentationSystem f
  exact properHenselian_baseChange_essSurj_of_properFPSystem f M

/-- The original finite-etale restriction functor is an equivalence for every
proper scheme over an arbitrary henselian local ring. -/
@[stacks 0A48]
theorem properHenselian_baseChange_isEquivalence :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).IsEquivalence := by
  apply ProperResidue.closedFiber_baseChange_isEquivalence_of_universal_essSurj
    (R := R) (π := f)
  intro Y g hg
  let := hg
  exact properHenselian_baseChange_essSurj g

/-- An explicit equivalence with the original closed-fibre functor as its forward map. -/
def properHenselianEquivalence :
    FiniteEtale X ≌ FiniteEtale (pullback f (LocalRing.residueSpecMap R)) := by
  let := properHenselian_baseChange_isEquivalence f
  exact (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).asEquivalence

@[simp]
theorem properHenselianEquivalence_functor :
    (properHenselianEquivalence f).functor =
      baseChange (pullback.fst f (LocalRing.residueSpecMap R)) := rfl

/-- Discharge the existing library comparison proposition with no extra hypotheses. -/
theorem properHenselianComparison : ProperHenselianComparison R := by
  intro Y g hg
  let := hg
  exact properHenselian_baseChange_isEquivalence g

end AlgebraicGeometry.Scheme.FiniteEtale
