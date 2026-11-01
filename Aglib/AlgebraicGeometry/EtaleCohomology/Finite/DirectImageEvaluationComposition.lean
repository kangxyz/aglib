/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.PointedEvaluationBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage

/-!
# Whole original pointed direct-image evaluation

The existing pointed evaluation is natural in the coefficient sheaf. Its
identity, composition and equality-transport laws retain the original site
comparisons, pointed stalk units and adjunction counits. No finiteness or
cohomology assumption enters these laws.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

open CoefficientStalkBaseChange

variable {Y X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (f : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X) (hy : y ≫ f = x)

/-- The original pointed stalk-unit isomorphism, transported from the existing
native stalk isomorphism along the specified point triangle. -/
def pointedStalkUnitNatIso :
    (pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      inverseImage f ⋙ (pointSmallEtale y).sheafFiber := by
  subst x
  exact StalkInverseImage.stalkUnitNatIso f y

/-- The whole isomorphism has the literal original pointed unit as its component. -/
@[simp] theorem pointedStalkUnitNatIso_hom_app (F : AbelianSheaf.{u, u + 1} X) :
    (pointedStalkUnitNatIso f y x hy).hom.app F = pointedStalkUnit f y F x hy := by
  subst x
  exact StalkInverseImage.stalkUnitNatIso_hom f y F

/-- The same original pointed evaluation, bundled naturally in its coefficient. -/
def pointedDirectImageEvaluationNatTrans :
    directImage f ⋙ (pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1}) ⟶
      (pointSmallEtale y).sheafFiber where
  app F := pointedDirectImageEvaluation f y x hy F
  naturality F G a := by
    let H := (pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1})
    dsimp only [Functor.comp_map]
    unfold pointedDirectImageEvaluation
    rw [← Category.assoc, pointedStalkUnit_naturality, Category.assoc, ← H.map_comp]
    have hc := (inverseImageAdjunction f).counit.naturality a
    dsimp only [Functor.comp_map, Functor.id_map] at hc
    rw [hc, H.map_comp, ← Category.assoc]

/-- Evaluation is definitionally the existing original stalk unit followed by counit. -/
theorem pointedDirectImageEvaluationNatTrans_app (F : AbelianSheaf.{u, u + 1} Y) :
    (pointedDirectImageEvaluationNatTrans f y x hy).app F =
      pointedDirectImageEvaluation f y x hy F := rfl

/-- Coefficient naturality is an equation on the original pointed evaluation maps. -/
@[reassoc]
theorem pointedDirectImageEvaluation_naturality
    {F G : AbelianSheaf.{u, u + 1} Y} (a : F ⟶ G) :
    (pointSmallEtale x).sheafFiber.map ((directImage f).map a) ≫
        pointedDirectImageEvaluation f y x hy G =
      pointedDirectImageEvaluation f y x hy F ≫ (pointSmallEtale y).sheafFiber.map a :=
  (pointedDirectImageEvaluationNatTrans f y x hy).naturality a

/-- The entire coefficient family factors through the existing natural stalk
unit isomorphism and the original inverse-image counit. -/
theorem pointedDirectImageEvaluationNatTrans_eq_unit_counit :
    pointedDirectImageEvaluationNatTrans f y (y ≫ f) rfl =
      Functor.whiskerLeft (directImage f) (StalkInverseImage.stalkUnitNatIso f y).hom ≫
        (Functor.associator (directImage f) (inverseImage f)
          ((pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1}))).inv ≫
        Functor.whiskerRight (inverseImageAdjunction f).counit
          ((pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
        (Functor.leftUnitor ((pointSmallEtale y).sheafFiber
          (A := AddCommGrpCat.{u + 1}))).hom := by
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    StalkInverseImage.stalkUnitNatIso_hom, Category.id_comp]
  rfl

/-- The whole original evaluation factors through the original pointed unit
isomorphism and counit for the given, possibly nonliteral point triangle. -/
theorem pointedDirectImageEvaluationNatTrans_eq_pointed_unit_counit :
    pointedDirectImageEvaluationNatTrans f y x hy =
      Functor.whiskerLeft (directImage f) (pointedStalkUnitNatIso f y x hy).hom ≫
        (Functor.associator (directImage f) (inverseImage f)
          ((pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1}))).inv ≫
        Functor.whiskerRight (inverseImageAdjunction f).counit
          ((pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
        (Functor.leftUnitor ((pointSmallEtale y).sheafFiber
          (A := AddCommGrpCat.{u + 1}))).hom := by
  subst x
  exact pointedDirectImageEvaluationNatTrans_eq_unit_counit f y

/-- The whole original pointed evaluation respects equality transport of its
scheme arrow, with the corresponding original direct-image transport. -/
theorem pointedDirectImageEvaluationNatTrans_congr {g : Y ⟶ X} (h : f = g)
    (hg : y ≫ g = x) :
    Functor.whiskerRight (eqToHom (congrArg (fun a : Y ⟶ X => directImage a) h))
        ((pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      pointedDirectImageEvaluationNatTrans g y x hg =
        pointedDirectImageEvaluationNatTrans f y x hy := by
  subst g
  simp only [eqToHom_refl, Functor.whiskerRight_id', Category.id_comp]

/-- The entire original identity evaluation is its original direct-image identity map. -/
theorem pointedDirectImageEvaluationNatTrans_id (x : Spec (.of Ω) ⟶ X) :
    pointedDirectImageEvaluationNatTrans (𝟙 X) x x (Category.comp_id x) =
      Functor.whiskerRight (directImageIdIso X).hom
          ((pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
        (Functor.leftUnitor ((pointSmallEtale x).sheafFiber
          (A := AddCommGrpCat.{u + 1}))).hom := by
  apply NatTrans.ext
  funext F
  let H := (pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hc₀ := conjugateEquiv_counit Adjunction.id (inverseImageAdjunction (𝟙 X))
    (inverseImageId X).hom F
  rw [conjugateEquiv_inverseImageId_hom] at hc₀
  change (inverseImage (𝟙 X)).map ((directImageIdIso X).inv.app F) ≫
    (inverseImageAdjunction (𝟙 X)).counit.app F = (inverseImageId X).hom.app F ≫ 𝟙 F at hc₀
  have hc₁ := hc₀.trans (Category.comp_id ((inverseImageId X).hom.app F))
  have hc : (inverseImageAdjunction (𝟙 X)).counit.app F =
      (inverseImageId X).hom.app ((directImage (𝟙 X)).obj F) ≫
        (directImageIdIso X).hom.app F := by
    apply (cancel_epi ((inverseImage (𝟙 X)).map ((directImageIdIso X).inv.app F))).mp
    rw [hc₁, ← Category.assoc]
    have hn := (inverseImageId X).hom.naturality ((directImageIdIso X).inv.app F)
    change (inverseImage (𝟙 X)).map ((directImageIdIso X).inv.app F) ≫
        (inverseImageId X).hom.app ((directImage (𝟙 X)).obj F) =
      (inverseImageId X).hom.app F ≫ (directImageIdIso X).inv.app F at hn
    rw [hn, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [pointedDirectImageEvaluationNatTrans_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  change pointedStalkUnit (𝟙 X) x ((directImage (𝟙 X)).obj F) x (Category.comp_id x) ≫
      H.map ((inverseImageAdjunction (𝟙 X)).counit.app F) =
    H.map ((directImageIdIso X).hom.app F)
  rw [hc, H.map_comp, ← Category.assoc, pointedStalkUnit_id, Category.id_comp]

variable {Z : Scheme.{u}} (g : Z ⟶ Y) (z : Spec (.of Ω) ⟶ Z) (hz : z ≫ g = y)

/-- Whole pointed evaluation composes through the original direct-image
comparison and associator, before evaluating a coefficient or a stalk element. -/
theorem pointedDirectImageEvaluationNatTrans_comp :
    Functor.whiskerRight (directImageCompIso f g).hom
        ((pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})) ≫
      pointedDirectImageEvaluationNatTrans (g ≫ f) z x
        (by rw [← Category.assoc, hz, hy]) =
      (Functor.associator (directImage g) (directImage f)
        ((pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1}))).hom ≫
        Functor.whiskerLeft (directImage g) (pointedDirectImageEvaluationNatTrans f y x hy) ≫
        pointedDirectImageEvaluationNatTrans g z y hz := by
  apply NatTrans.ext
  funext F
  let H := (pointSmallEtale z).sheafFiber (A := AddCommGrpCat.{u + 1})
  let P := (directImage f).obj ((directImage g).obj F)
  have hc := conjugateEquiv_counit
    ((inverseImageAdjunction f).comp (inverseImageAdjunction g))
    (inverseImageAdjunction (g ≫ f)) (inverseImageComp f g).hom F
  rw [conjugateEquiv_inverseImageComp_hom] at hc
  change (inverseImage (g ≫ f)).map ((directImageCompIso f g).hom.app F) ≫
      (inverseImageAdjunction (g ≫ f)).counit.app F =
    (inverseImageComp f g).hom.app P ≫
      (inverseImage g).map ((inverseImageAdjunction f).counit.app ((directImage g).obj F)) ≫
        (inverseImageAdjunction g).counit.app F at hc
  have hu := pointedStalkUnit_comp f y P g z x hz hy
  have hn := pointedStalkUnit_naturality (g ≫ f) z x
    (by rw [← Category.assoc, hz, hy]) ((directImageCompIso f g).hom.app F)
  have hm := pointedStalkUnit_naturality g z y hz
    ((inverseImageAdjunction f).counit.app ((directImage g).obj F))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, pointedDirectImageEvaluationNatTrans_app]
  unfold pointedDirectImageEvaluation
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← H.map_comp, hc, H.map_comp, H.map_comp,
    reassoc_of% hu, ← reassoc_of% hm]

/-- Component composition is the evaluation of the proved whole natural-transformation law. -/
theorem pointedDirectImageEvaluation_comp (F : AbelianSheaf.{u, u + 1} Z) :
    (pointSmallEtale x).sheafFiber.map ((directImageCompIso f g).hom.app F) ≫
        pointedDirectImageEvaluation (g ≫ f) z x (by rw [← Category.assoc, hz, hy]) F =
      pointedDirectImageEvaluation f y x hy ((directImage g).obj F) ≫
        pointedDirectImageEvaluation g z y hz F := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, pointedDirectImageEvaluationNatTrans_app] using
      NatTrans.congr_app (pointedDirectImageEvaluationNatTrans_comp f y x hy g z hz) F

end AlgebraicGeometry.Scheme.EtaleCohomology
