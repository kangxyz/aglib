/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedFiniteCover
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedOverlap
public import Aglib.AlgebraicGeometry.Modules.Coherent.FiniteCoverQuotientDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The genuine coherent quotient of the degree-zero ambient pullback

The local modules and quotient maps are those of the original formal system.
Only their coherent relation kernels are glued, and the global object is the
actual cokernel of the glued relation inclusion.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
  (I : Ideal A) (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- A finite original affine cover yields a genuine coherent graded coefficient
with its original local presentations and quotient equations retained. -/
theorem exists_formalGradedCoherentQuotient_on_cover
    {ι : Type u} [Finite ι] (U : ι → X.affineOpens)
    (hU : ∀ x : X, ∃ i, x ∈ (U i).val) :
    letI (V : X.Opens) : Algebra A Γ(X, V) := formalGradedSectionAlgebra f V
    ∃ (G : QuasiCoherent.FiniteTypeSheaves (formalGradedSpace f I))
      (q : formalGradedAmbient f I F ⟶ G.obj), Epi q ∧
      ∃ (e : ∀ i, G.obj.restrict (formalGradedChart f I (U i)) ≅
          tilde (R := CommRingCat.of (Γ(X, U i) ⊗[A] I.associatedGraded))
            (formalGradedLocalModule f I F (U i))),
        ∀ i, (Scheme.Modules.restrictFunctor (formalGradedChart f I (U i))).map q ≫ (e i).hom =
          formalGradedLocalQuotient f I F (U i) := by
  let (V : X.Opens) : Algebra A Γ(X, V) := formalGradedSectionAlgebra f V
  let W (i k : ι) : X.affineOpens :=
    ⟨(U i).val ⊓ (U k).val, (U i).property.inf (U k).property⟩
  exact exists_coherent_quotient_of_finite_openImmersionCover
    (fun i => Spec (CommRingCat.of (Γ(X, U i) ⊗[A] I.associatedGraded)))
    (fun i => formalGradedChart f I (U i)) (formalGradedCharts_cover f I U hU)
    (formalGradedAmbient f I F) (formalGradedAmbient_finite f I F)
    (fun i => tilde (R := CommRingCat.of (Γ(X, U i) ⊗[A] I.associatedGraded))
            (formalGradedLocalModule f I F (U i)))
    (fun i => formalGradedLocalQuotient_finite f I F (U i))
    (fun i => formalGradedLocalQuotient f I F (U i))
    (fun i k => formalGradedOverlapIso f I F (U i) (U k) (W i k)
      inf_le_left inf_le_right rfl)
    (fun i k => formalGradedOverlapIso_quotient f I F (U i) (U k) (W i k)
      inf_le_left inf_le_right rfl)

end AlgebraicGeometry.Scheme.Cohomology
