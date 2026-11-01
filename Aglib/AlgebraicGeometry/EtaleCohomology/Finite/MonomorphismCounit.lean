/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GlobalEvaluationIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse
public import Mathlib.Algebra.Group.Equiv.Basic

/-! # The original counit for a finite monomorphism

Over the image of an original geometric point, the geometric fibre of a
monomorphism has exactly that point. The original finite direct-image stalk
tuple therefore has an invertible coordinate evaluation. Its defining
formula is the original stalk unit followed by the stalk of the original
adjunction counit. Since the stalk unit is invertible, the counit is invertible
on all original geometric stalks, and consequently on the original sheaves.
No surjectivity, constructibility or coefficient-order hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

open CoefficientStalkBaseChange
attribute [local instance] hasSheafifyLarge

/-- The original pointed evaluation for a finite monomorphism is invertible:
the literal geometric fibre over the image point is a singleton. -/
theorem finiteMono_pointedDirectImageEvaluation_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Mono f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso (pointedDirectImageEvaluation f x (x ≫ f) rfl F) := by
  let J := {y : Spec (.of Ω) ⟶ X // y ≫ f = x ≫ f}
  let : Unique J := {
    default := ⟨x, rfl⟩
    uniq := fun y => Subtype.ext ((cancel_mono f).mp y.property) }
  have ht : IsIso (directImageEvaluationTuple f (x ≫ f) F) :=
    finiteDirectImageEvaluationTuple_isIso f (x ≫ f) F
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun a => directImageEvaluationTuple f (x ≫ f) F a ⟨x, rfl⟩)
  exact (AddEquiv.piUnique (fun y : J => coefficientFiber y.val F)).bijective.comp
    (ConcreteCategory.bijective_of_isIso (directImageEvaluationTuple f (x ≫ f) F))

/-- The original adjunction counit of a finite monomorphism is an isomorphism
for every original abelian sheaf. -/
theorem finiteMono_counit_app_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Mono f]
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((inverseImageAdjunction f).counit.app F) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 X)
  intro Ω _ _ x _
  have hu : IsIso (pointedStalkUnit f x ((directImage f).obj F) (x ≫ f) rfl) := by
    change IsIso (stalkUnit f x ((directImage f).obj F))
    infer_instance
  have he := finiteMono_pointedDirectImageEvaluation_isIso f x F
  change IsIso (pointedStalkUnit f x ((directImage f).obj F) (x ≫ f) rfl ≫
    (pointSmallEtale x).sheafFiber.map ((inverseImageAdjunction f).counit.app F)) at he
  exact (isIso_comp_left_iff _ _).mp he

/-- The whole original counit natural transformation is invertible. -/
theorem finiteMono_counit_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Mono f] :
    IsIso (inverseImageAdjunction f).counit := by
  have (F : AbelianSheaf.{u, u + 1} X) :
      IsIso ((inverseImageAdjunction f).counit.app F) := finiteMono_counit_app_isIso f F
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
