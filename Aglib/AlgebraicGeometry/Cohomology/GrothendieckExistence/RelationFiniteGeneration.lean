/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationHomogeneousAction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationKernelBound
public import Aglib.RingTheory.AssociatedGraded.TensorComponentGeneration
public import Aglib.RingTheory.AssociatedGraded.TensorRing
public import Aglib.RingTheory.AssociatedGraded.NativeRing

/-! # The finite actual graded relation module supplies the original kernel bound -/

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
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)
  (U : X.affineOpens)
  [Algebra A Γ(X, U.1)]
  [Module I.associatedGraded (⨁ n, Γ(relationGradedPiece φ n, U.1))]
  [Module (Γ(X, U.1) ⊗[A] I.associatedGraded)
    (⨁ n, Γ(relationGradedPiece φ n, U.1))]

omit [Algebra A Γ(X, U.1)]
    [Module I.associatedGraded (⨁ n, Γ(relationGradedPiece φ n, U.1))]
    [Module (Γ(X, U.1) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(relationGradedPiece φ n, U.1))] in
/-- Native homogeneous classes have original ideal-power representatives,
so the actual component products are original scalar relation products. -/
theorem positiveComponentProducts_subset_relationPositiveSections (c j : ℕ) :
    GradedModule.positiveComponentProducts A I.associatedGraded I.associatedGradedGrading
      (fun n => (Γ(relationGradedPiece φ n, U.1) : Type u))
      (fun r n a y => (relationGradedHomogeneousAction f I φ r n a).app U.1 y) c j ⊆
        relationPositiveSections f I φ c j U.1 := by
  intro z hz
  obtain ⟨r, n, he, hr, hn, a, y, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := I.associatedGradedComponentMap_surjective r a
  refine ⟨r, n, he, hr, hn, b, y, ?_⟩
  simp only [relationGradedHomogeneousAction_componentMap]

/-- Finiteness of the actual tensor-coefficient module, with its original
homogeneous action, supplies bounded positive generation on original sections.
This is the algebraic input obtained from the coherent graded kernel realization. -/
theorem exists_relationPositiveSections_span_of_finite
    (hact : ∀ r n (a : I.associatedGradedGrading r)
      (y : Γ(relationGradedPiece φ n, U.1)),
      (a : I.associatedGraded) • DirectSum.of (fun k => Γ(relationGradedPiece φ k, U.1)) n y =
        DirectSum.of (fun k => Γ(relationGradedPiece φ k, U.1)) (r + n)
          ((relationGradedHomogeneousAction f I φ r n a).app U.1 y))
    (htmul : ∀ (b : Γ(X, U.1)) (s : I.associatedGraded)
      (x : ⨁ n, Γ(relationGradedPiece φ n, U.1)), (b ⊗ₜ[A] s) • x = b • s • x)
    [Module.Finite (Γ(X, U.1) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(relationGradedPiece φ n, U.1))] :
    ∃ c : ℕ, ∀ j, c < j →
      Submodule.span Γ(X, U.1) (relationPositiveSections f I φ c j U.1) = ⊤ := by
  obtain ⟨c, hc⟩ := GradedModule.exists_span_positiveComponentProducts
    A Γ(X, U.1) I.associatedGraded I.associatedGradedGrading
    (fun n => (Γ(relationGradedPiece φ n, U.1) : Type u))
    (fun r n a y => (relationGradedHomogeneousAction f I φ r n a).app U.1 y) hact htmul
  refine ⟨c, fun j hj => top_unique ?_⟩
  rw [← hc j hj]
  exact Submodule.span_mono
    (positiveComponentProducts_subset_relationPositiveSections f I φ U c j)

end AlgebraicGeometry.Scheme.Cohomology
