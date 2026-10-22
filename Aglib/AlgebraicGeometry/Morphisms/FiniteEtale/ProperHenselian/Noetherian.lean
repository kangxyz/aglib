/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperGeometricBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.OverIso
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperSubalgebraModel
public import Aglib.RingTheory.Localization.IntegerLocalTarget

/-!
# Finite-etale covers over a proper Noetherian henselian local base

The original closed-fibre pullback is an equivalence. Actual arithmetic models,
marked residue-field object descent, and geometric local Artin approximation
supply essential surjectivity; the original graph argument supplies fullness.
No excellence, flatness, projectivity or dimension hypothesis is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

/-- Actual closed-fibre covers lift for proper finitely presented schemes over
any henselian local ring. The finite-presentation premise is explicit; this
statement does not assert arbitrary-base proper approximation. -/
theorem properHenselian_baseChange_essSurj_of_finitePresentation
    [LocallyOfFinitePresentation f] :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).EssSurj := by
  let D := Localization.IntegerLocalTarget.Ring R
  let : Algebra D R := (Localization.IntegerLocalTarget.map R).toAlgebra
  obtain ⟨s, M, hM⟩ :=
    FiniteTypeSubalgebraLimit.exists_properModel_over_finiteTypeSubalgebra D R f
  let B := Algebra.FiniteTypeSubalgebraLimit.stage D R s
  let : IsProper M.f := hM
  let : (baseChange (pullback.fst (pullback.snd M.f (Spec.algebraMap B R))
      (LocalRing.residueSpecMap R))).EssSurj :=
    properGeometricBaseChange_essSurj D B R M.f
  exact baseChange_essSurj_of_overIso (LocalRing.residueSpecMap R) f
    (pullback.snd M.f (Spec.algebraMap B R)) M.overIso

variable [IsNoetherianRing R]

/-- The original finite-etale closed-fibre pullback of a proper scheme over
an arbitrary Noetherian henselian local ring is essentially surjective. -/
theorem properNoetherianHenselian_baseChange_essSurj :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).EssSurj :=
  properHenselian_baseChange_essSurj_of_finitePresentation f

/-- The literal closed-fibre functor is an equivalence, with no auxiliary
model, approximation, or lifting premise. -/
theorem properNoetherianHenselian_baseChange_isEquivalence :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).IsEquivalence := by
  apply ProperResidue.closedFiber_baseChange_isEquivalence_of_universal_essSurj
    (R := R) (π := f)
  intro Y g hg
  let := hg
  exact properNoetherianHenselian_baseChange_essSurj g

/-- An explicit equivalence whose forward functor is the original native
finite-etale closed-fibre pullback. -/
def properNoetherianHenselianEquivalence :
    FiniteEtale X ≌ FiniteEtale (pullback f (LocalRing.residueSpecMap R)) := by
  let := properNoetherianHenselian_baseChange_isEquivalence f
  exact (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).asEquivalence

@[simp]
theorem properNoetherianHenselianEquivalence_functor :
    (properNoetherianHenselianEquivalence f).functor =
      baseChange (pullback.fst f (LocalRing.residueSpecMap R)) := rfl

/-- Discharge the library's existing proper-henselian comparison proposition
for every Noetherian henselian local ring, retaining its original definition. -/
theorem properHenselianComparison_of_noetherian : ProperHenselianComparison R := by
  intro Y g hg
  let := hg
  exact properNoetherianHenselian_baseChange_isEquivalence g

end AlgebraicGeometry.Scheme.FiniteEtale
