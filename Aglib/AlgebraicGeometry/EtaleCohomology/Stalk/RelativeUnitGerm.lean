/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitGeometry
public import Aglib.CategoryTheory.Sites.Point.RelativeTest

/-! # Original relative-terminal unit sections and their pointed germs

The actual relative terminal test lifts the actual field point. Consequently
its original unit section has precisely the original stalk-unit germ. No
cohomological or geometric base-change isomorphism is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem relativeTerminalTest_point {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) (b : T ⟶ U.left) (h : b ≫ U.hom = g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ T)
    (p : (pointSmallEtale (η ≫ g)).fiber.obj U) (hp : p.left = η ≫ b)
    (t : (pointSmallEtale η).fiber.obj (etaleTerminal T)) :
    (pointSmallEtale η).fiber.map (Continuity.relativeTerminalTest g U b h) t =
      CoefficientStalkBaseChange.pulledBackPoint g η U p := by
  apply Over.OverMorphism.ext
  change t.left ≫ pullback.lift b (𝟙 T) _ = _
  have he := CoefficientStalkBaseChange.pointedPulledBackPoint_left
    g η (η ≫ g) rfl U p
  change (CoefficientStalkBaseChange.pulledBackPoint g η U p).left =
    pullback.lift p.left η _ at he
  rw [he]
  have ht : t.left = η := (Category.comp_id t.left).symm.trans (Over.w t)
  exact GrothendieckTopology.Point.relativeTest_comp_lift U.hom g b h η p.left
    (Over.w p) hp t.left ht

/-- The original relative-terminal unit section represents the original
stalk-unit image of the same pointed chart section. -/
theorem unitSectionMap_relativeTerminalTest_germ {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) (b : T ⟶ U.left) (h : b ≫ U.hom = g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ T)
    (F : AbelianSheaf.{u, u + 1} S)
    (p : (pointSmallEtale (η ≫ g)).fiber.obj U) (hp : p.left = η ≫ b)
    (t : (pointSmallEtale η).fiber.obj (etaleTerminal T)) :
    (pointSmallEtale (η ≫ g)).toPresheafFiber U p F.obj ≫
        (StalkInverseImage.stalkUnitNatIso g η).hom.app F =
      Continuity.unitSectionMap g F (Continuity.relativeTerminalTest g U b h) ≫
        (pointSmallEtale η).toPresheafFiber (etaleTerminal T) t
          ((inverseImage g).obj F).obj := by
  refine (StalkInverseImage.germ_stalkUnitNatIso g η F U p).trans ?_
  exact (pointSmallEtale η).germ_after_test ((inverseImage g).obj F).obj
    (((inverseImageAdjunction g).unit.app F).hom.app (op U))
    (Continuity.relativeTerminalTest g U b h) t
    (CoefficientStalkBaseChange.pulledBackPoint g η U p)
    (relativeTerminalTest_point g U b h η p hp t)

end AlgebraicGeometry.Scheme.EtaleCohomology
