/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperCompleteLocal
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteTypeCoefficient
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.ComparisonSquare
public import Aglib.RingTheory.AdicCompletion.NoetherianRing

/-!
# The geometric consumer of exact algebra-map approximation

This is an intermediate implication with an explicitly quantified approximation
premise. The geometric-local public theorems discharge that premise using the
proved field and DVR Artin approximation theorems. Actual covers and the
original closed-fibre comparison are retained throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

/-- Exact algebra-map approximation at order one suffices to algebraize every
actual finite-etale cover of the literal closed fibre of a proper scheme. -/
theorem properLocal_baseChange_essSurj_of_approximation
    (hApprox : ∀ (C : Type u) [CommRing C] [Algebra R C]
      [Algebra.FinitePresentation R C]
      (b : C →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R),
      ∃ a : C →ₐ[R] R,
        (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal R ^ 1)).comp a =
          (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) 1).comp b) :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap R))).EssSurj := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : IsNoetherianRing A := AdicCompletion.isNoetherianRing R _
  let fA := pullback.snd f (LocalRing.completionSpecMap R)
  let e := LocalRing.completionResidueFiberIso f
  let iA := pullback.fst fA (LocalRing.residueSpecMap A)
  let F := baseChange iA
  let : F.EssSurj := properCompleteLocal_baseChange_essSurj fA
  constructor
  intro C₀
  obtain ⟨Y, ⟨d₀⟩⟩ := Functor.EssSurj.mem_essImage F ((baseChange e.hom).obj C₀)
  obtain ⟨s, Ys, ⟨ds⟩⟩ :=
    LimitDescent.exists_cover_over_finiteTypeSubalgebra R A f Y
  let C := Algebra.FiniteTypeSubalgebraLimit.stage R A s
  let : Algebra.FinitePresentation R C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨a, ha⟩ := hApprox C C.val
  refine ⟨(baseChange (LocalRing.algebraSpecialization f a)).obj Ys, ⟨?_⟩⟩
  exact originalCoverIsoOfComparisonSquare
    (LocalRing.algebraSpecialization f a) (LocalRing.coefficientBaseChangeMap f C.val)
    (pullback.fst f (LocalRing.residueSpecMap R)) iA e
    (LocalRing.completionSpecialization_square f a C.val ha) Ys C₀
    ((baseChange iA).mapIso ds ≪≫ d₀)

end AlgebraicGeometry.Scheme.FiniteEtale
