/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Right exactness of coherent completion in the ambient diagram category

Ordinary reduction is right exact, pointwise in the native inverse diagram.
This statement does not equip the category of adic systems with cokernels or
an abelian structure, and does not assert left exactness of ordinary reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (K : X.IdealSheafData)

/-- Ordinary closed-thickening reduction preserves colimits. -/
instance idealSheafQuotientFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (idealSheafQuotientFunctor X K) := by
  dsimp only [idealSheafQuotientFunctor]
  infer_instance

variable [IsLocallyNoetherian X]

/-- Coherent completion considered in the native ambient inverse-diagram category. -/
abbrev ambientCompletion : X.CoherentSheaf ⥤ (ℕᵒᵖ ⥤ X.Modules) :=
  completionFunctor X K ⋙ adicSystemToDiagram X K

/-- The original pointwise completion is right exact. No formal-system
cokernels or formal-system abelian structure enter this proof. -/
instance ambientCompletion_preservesFiniteColimits :
    PreservesFiniteColimits (ambientCompletion X K) := by
  apply preservesFiniteColimits_of_evaluation
  intro n
  change PreservesFiniteColimits
    (QuasiCoherent.finiteTypeSheavesToModules X ⋙
      idealSheafQuotientFunctor X (K ^ n.unop))
  infer_instance

/-- The original completion maps zero coefficient maps to zero diagrams. -/
instance ambientCompletion_preservesZeroMorphisms :
    (ambientCompletion X K).PreservesZeroMorphisms where
  map_zero F G := by
    apply NatTrans.ext
    funext n
    change (idealSheafQuotientFunctor X (K ^ n.unop)).map (0 : F.obj ⟶ G.obj) = 0
    exact (idealSheafQuotientFunctor X (K ^ n.unop)).map_zero _ _

end AlgebraicGeometry.Scheme.Modules.Coherent
