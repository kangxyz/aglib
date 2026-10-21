/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationAffineAction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationFiniteGeneration
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineFinite
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedChartNoetherian

/-! # The original relation-kernel bound on every affine open -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite DirectSum
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f] (I : Ideal A)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

/-- The actual ordinary relation tower has an ideal-valued reduction-kernel
bound on each affine open. Graded finiteness, homogeneous span, and all scalar
lifts are constructed from the original levelwise epimorphism. -/
theorem exists_relation_kernel_bound_on_affine (U : X.affineOpens)
    (hφ : ∀ n, Epi (φ.hom.app (op n))) :
    ∃ c : ℕ, ∀ m (h : c + 1 ≤ m),
      ((relationMap φ h).val.app (op U.1)).hom.ker ≤
        (idealThickeningIdealSheaf f I).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(relation φ m, U.1)) := by
  let : Algebra A Γ(X, U.1) := formalGradedSectionAlgebra f U.1
  let : Module (Γ(X, U.1) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(P.gradedPiece n, U.1)) := formalGradedAffineModule f I P U.1
  let : IsNoetherianRing (Γ(X, U.1) ⊗[A] I.associatedGraded) :=
    formalGradedChart_noetherian f I U
  let : Module.Finite (Γ(X, U.1) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(P.gradedPiece n, U.1)) := formalGradedAffineModule_finite f I P U.1 U.property
  let : Module (Γ(X, U.1) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(relationGradedPiece φ n, U.1)) := relationGradedAffineModule f I U.1 φ
  let : Module I.associatedGraded (⨁ n, Γ(relationGradedPiece φ n, U.1)) :=
    relationGradedExternalModule f I U.1 φ
  let : Module.Finite (Γ(X, U.1) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(relationGradedPiece φ n, U.1)) := relationGradedAffineModule_finite f I U.1 φ
  obtain ⟨c, hc⟩ := exists_relationPositiveSections_span_of_finite f I φ U
    (relationGradedExternalModule_smul f I U.1 φ)
    (relationGradedAffineModule_tmul_smul f I U.1 φ)
  refine ⟨c, fun m h => ?_⟩
  let := hφ m
  exact relation_kernel_le_ideal_of_homogeneous_span f I φ c m U
    (fun j hj _ => hc j hj) h

end AlgebraicGeometry.Scheme.Cohomology
