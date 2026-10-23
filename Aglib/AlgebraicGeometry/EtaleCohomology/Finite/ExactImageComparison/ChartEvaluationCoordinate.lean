/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.ChartStalkComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.ChartEvaluationIndex

/-! # Original chart evaluation in its actual affine finite coordinate -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

open CoefficientStalkBaseChange
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
  (R Ω : Type u) [CommRing R] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
  (g : Spec (.of R) ⟶ S) [Etale g]
  (s : Spec (.of Ω) ⟶ S) (hs : Spec.algebraMap R Ω ≫ g = s)
  (F : AbelianSheaf.{u, u + 1} X)

/-- The coordinate isomorphism is the literal original point stalk unit. -/
def finiteChartPointStalkIso (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = s}) :
    coefficientFiber x.val F ≅
      coefficientFiber (finiteAffineExtendedPoint R Ω (pullback.fst g f)
        ((finiteChartEvaluationIndex f R Ω g s hs).symm x))
        ((inverseImage (pullback.snd g f)).obj F) := by
  let η := finiteAffineExtendedPoint R Ω (pullback.fst g f)
    ((finiteChartEvaluationIndex f R Ω g s hs).symm x)
  let hm := finiteChartEvaluationIndex_symm_point f R Ω g s hs x
  let := pointedStalkUnit_isIso (pullback.snd g f) η x.val hm F
  exact asIso (pointedStalkUnit (pullback.snd g f) η F x.val hm)

/-- The original comparison's actual affine coordinate equals original
geometric evaluation followed by the original point-unit isomorphism. -/
theorem finiteChartEvaluation_coordinate
    (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = s})
    (z : coefficientFiber s ((directImage f).obj F)) :
    (finiteAffineExtendedStalkIso R Ω (pullback.fst g f)
      ((inverseImage (pullback.snd g f)).obj F)).hom
      ((directImageChartStalkIso f g (Spec.algebraMap R Ω) s hs F).hom z)
      ((finiteChartEvaluationIndex f R Ω g s hs).symm x) =
    (finiteChartPointStalkIso f R Ω g s hs F x).hom
      (pointedDirectImageEvaluation f x.val s x.property F z) := by
  rw [finiteAffineExtendedStalkIso_apply, finiteAffineExtendedCoordinate_eq_evaluation]
  exact ConcreteCategory.congr_hom
    (directImageChartStalkIso_evaluation f g (Spec.algebraMap R Ω) s hs F x.val
      (finiteAffineExtendedPoint R Ω (pullback.fst g f)
        ((finiteChartEvaluationIndex f R Ω g s hs).symm x)) x.property
      (finiteAffineExtendedPoint_comp R Ω (pullback.fst g f)
        ((finiteChartEvaluationIndex f R Ω g s hs).symm x))
      (finiteChartEvaluationIndex_symm_point f R Ω g s hs x)) z

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
