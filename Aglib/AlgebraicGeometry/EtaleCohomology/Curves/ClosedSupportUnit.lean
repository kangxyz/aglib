/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GlobalEvaluationIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-!
# The original unit for coefficients supported on a closed subscheme

This specializes the published finite direct-image evaluation theorem. Support
is expressed at the original geometric stalks outside the geometric image.
The resulting isomorphism is the actual inverse-image/direct-image unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

open CoefficientStalkBaseChange

universe u

attribute [local instance] hasSheafifyLarge

private theorem unit_evaluation {Z X : Scheme.{u}} (i : Z ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Z)
    (s : Spec (.of Ω) ⟶ X) (hz : z ≫ i = s) (F : AbelianSheaf.{u, u + 1} X) :
    (pointSmallEtale s).sheafFiber.map ((inverseImageAdjunction i).unit.app F) ≫
      pointedDirectImageEvaluation i z s hz ((inverseImage i).obj F) =
        pointedStalkUnit i z F s hz := by
  let H := (pointSmallEtale z).sheafFiber (A := Ab.{u + 1})
  have hn : (pointSmallEtale s).sheafFiber.map ((inverseImageAdjunction i).unit.app F) ≫
      pointedStalkUnit i z ((directImage i).obj ((inverseImage i).obj F)) s hz =
      pointedStalkUnit i z F s hz ≫
        H.map ((inverseImage i).map ((inverseImageAdjunction i).unit.app F)) :=
    pointedStalkUnit_naturality i z s hz ((inverseImageAdjunction i).unit.app F)
  rw [pointedDirectImageEvaluation, ← Category.assoc, hn]
  change pointedStalkUnit i z F s hz ≫ H.map _ ≫ H.map _ = _
  rw [← H.map_comp, (inverseImageAdjunction i).left_triangle_components,
    CategoryTheory.Functor.map_id, Category.comp_id]

private theorem pointed_unit_isIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Z)
    (s : Spec (.of Ω) ⟶ X) (hz : z ≫ i = s) (F : AbelianSheaf.{u, u + 1} X) :
    IsIso (pointedStalkUnit i z F s hz) := by
  subst s
  exact StalkInverseImage.stalkUnit_isIso i z F

/-- The literal adjunction unit is invertible at one geometric point when its
original stalk vanishes if that point has no lift through the finite monomorphism. -/
theorem supported_unit_stalk_isIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsFinite i] [Mono i] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (hF : (∀ z : Spec (.of Ω) ⟶ Z, z ≫ i ≠ s) → IsZero (coefficientFiber s F)) :
    IsIso ((pointSmallEtale s).sheafFiber.map ((inverseImageAdjunction i).unit.app F)) := by
  let I := {z : Spec (.of Ω) ⟶ Z // z ≫ i = s}
  let : Subsingleton I :=
    ⟨fun z t => Subtype.ext ((cancel_mono i).mp (z.property.trans t.property.symm))⟩
  let a := (pointSmallEtale s).sheafFiber.map ((inverseImageAdjunction i).unit.app F)
  let e := directImageEvaluationTuple i s ((inverseImage i).obj F)
  let : IsIso e := Finite.finiteDirectImageEvaluationTuple_isIso i s ((inverseImage i).obj F)
  have he : Function.Bijective e := (ConcreteCategory.isIso_iff_bijective e).mp inferInstance
  apply (ConcreteCategory.isIso_iff_bijective a).mpr
  apply (Function.Bijective.of_comp_iff' he a).mp
  by_cases hI : Nonempty I
  · obtain ⟨z⟩ := hI
    let t := pointedStalkUnit i z.val F s z.property
    let : IsIso t := pointed_unit_isIso i z.val s z.property F
    have ht : Function.Bijective t := (ConcreteCategory.isIso_iff_bijective t).mp inferInstance
    have hc (b : coefficientFiber s F) (y : I) : e (a b) y =
        pointedStalkUnit i y.val F s y.property b :=
      ConcreteCategory.congr_hom (unit_evaluation i y.val s y.property F) b
    constructor
    · intro b c h
      apply ht.injective
      exact (hc b z).symm.trans ((congrFun h z).trans (hc c z))
    · intro b
      obtain ⟨c, hc'⟩ := ht.surjective (b z)
      refine ⟨c, funext fun y => ?_⟩
      have hy : y = z := Subsingleton.elim y z
      rw [hy]
      exact (hc c z).trans hc'
  · have hsource := hF (fun z hz => hI ⟨⟨z, hz⟩⟩)
    let : Subsingleton (coefficientFiber s F) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp hsource
    let : IsEmpty I := ⟨fun z => hI ⟨z⟩⟩
    constructor
    · intro b c _
      exact @Subsingleton.elim (coefficientFiber s F) inferInstance b c
    · intro b
      exact ⟨0, funext fun z => isEmptyElim z⟩

/-- The actual unit is invertible for coefficients supported on the geometric image of a
closed immersion. The stated support premise concerns the original geometric stalks. -/
theorem closedSupportUnit_isIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : AbelianSheaf.{u, u + 1} X)
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      (∀ z : Spec (.of Ω) ⟶ Z, z ≫ i ≠ s) → IsZero (coefficientFiber s F)) :
    IsIso ((inverseImageAdjunction i).unit.app F) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 X)
  intro Ω _ _ s _
  exact supported_unit_stalk_isIso i s F (hF Ω s)

/-- The small native conservative family suffices for the supported-unit criterion. -/
theorem closedSupportUnit_isIso_of_pointFamily {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : AbelianSheaf.{u, u + 1} X)
    (hF : ∀ x : X,
      (∀ z : Spec (.of (FibrewiseClosed.pointField x)) ⟶ Z,
        z ≫ i ≠ FibrewiseClosed.geometricPoint x) →
      IsZero (coefficientFiber (FibrewiseClosed.geometricPoint x) F)) :
    IsIso ((inverseImageAdjunction i).unit.app F) := by
  apply StalkUniverse.isIso_of_original_geometricStalks (𝟙 X)
  intro x
  exact supported_unit_stalk_isIso i (FibrewiseClosed.geometricPoint x.val) F (hF x.val)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
