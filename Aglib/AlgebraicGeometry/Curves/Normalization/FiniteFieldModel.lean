/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.SubalgebraColimit
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperSubalgebraModel
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Proper models over actual finite field stages

The original finite-generated subalgebras of the algebraic closure are already
finite extensions of the coefficient field. The existing scheme-model and
properness descent constructions produce a proper model at one of these same
stages, retaining its actual inclusion and cartesian comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.FiniteTypeSubalgebraLimit
open AlgebraicGeometry.Scheme.FinitePresentationDescent

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Normalization.FiniteField

variable (K : Type u) [Field K]

/-- The original finite-generated subalgebra stage, not a replacement field. -/
abbrev stage (s : Finset (AlgebraicClosure K)) :=
  Algebra.FiniteTypeSubalgebraLimit.stage K (AlgebraicClosure K) s

instance stage_integral (s : Finset (AlgebraicClosure K)) :
    Algebra.IsIntegral K (stage K s) :=
  (Subalgebra.isIntegral_iff _).mpr fun x _ => Algebra.IsIntegral.isIntegral x

/-- Algebraicity makes each original finite-generated stage a finite field. -/
instance stage_field (s : Finset (AlgebraicClosure K)) : Field (stage K s) :=
  (isField_of_isIntegral_of_isField' (R := K) (S := stage K s)
    (Field.toIsField K)).toField

instance stage_finite (s : Finset (AlgebraicClosure K)) : Module.Finite K (stage K s) :=
  Algebra.IsIntegral.finite

/-- A proper scheme over the original algebraic closure descends to a proper
model over one actual finite field stage. The comparison square is part of the
constructed model, rather than an external descent certificate. -/
theorem exists_proper_model
    {X : Scheme.{u}} (f : X ⟶ Spec (.of (AlgebraicClosure K))) [IsProper f] :
    ∃ s : Finset (AlgebraicClosure K),
      ∃ M : Model (Spec.map (CommRingCat.ofHom (stage K s).val.toRingHom)) f,
        IsProper M.f :=
  Scheme.FiniteTypeSubalgebraLimit.exists_properModel_over_finiteTypeSubalgebra_of_noetherian
    K (AlgebraicClosure K) f

end AlgebraicGeometry.Scheme.OverField.Curve.Normalization.FiniteField
