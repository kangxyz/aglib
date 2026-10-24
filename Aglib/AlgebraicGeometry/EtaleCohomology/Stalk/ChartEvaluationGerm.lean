/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitSections

/-! # Original chart evaluation and the original geometric germ

The original chart-evaluation inverse identifies a represented section germ
with the terminal germ after the original stalk-unit comparison. The proof
uses the actual chart diagonal and the actual pulled-back field point.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem chartDiagonal_point {S : Scheme.{u}} (U : S.Etale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ U.left)
    (p : (pointSmallEtale η).fiber.obj (etaleTerminal U.left)) :
    (pointSmallEtale η).fiber.map (Continuity.chartDiagonal U) p =
      CoefficientStalkBaseChange.pulledBackPoint U.hom η U (Over.homMk η rfl) := by
  apply Over.OverMorphism.ext
  change p.left ≫ pullback.diagonal U.hom = _
  have h := CoefficientStalkBaseChange.pointedPulledBackPoint_left
    U.hom η (η ≫ U.hom) rfl U (Over.homMk η rfl)
  change (CoefficientStalkBaseChange.pulledBackPoint U.hom η U
    (Over.homMk η rfl)).left = pullback.lift η η _ at h
  rw [h]
  have hp : p.left = η := (Category.comp_id p.left).symm.trans (Over.w p)
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.diagonal_fst, pullback.lift_fst,
      Category.comp_id] using hp
  · simpa only [Category.assoc, pullback.diagonal_snd, pullback.lift_snd,
      Category.comp_id] using hp

/-- The original chart-section comparison preserves the actual original germ
under the original inverse-image stalk-unit isomorphism. -/
theorem pullbackSectionsEtaleEvaluationIso_germ {S : Scheme.{u}} (U : S.Etale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ U.left)
    (F : AbelianSheaf.{u, u + 1} S)
    (p : (pointSmallEtale η).fiber.obj (etaleTerminal U.left)) :
    (pointSmallEtale (η ≫ U.hom)).toPresheafFiber U (Over.homMk η rfl) F.obj ≫
        (StalkInverseImage.stalkUnitNatIso U.hom η).hom.app F =
      (Continuity.pullbackSectionsEtaleEvaluationIso F U).inv ≫
        (pointSmallEtale η).toPresheafFiber (etaleTerminal U.left) p
          ((inverseImage U.hom).obj F).obj := by
  have h := (pointSmallEtale η).toPresheafFiber_w (Continuity.chartDiagonal U) p
    ((inverseImage U.hom).obj F).obj
  rw [chartDiagonal_point U η p] at h
  rw [StalkInverseImage.germ_stalkUnitNatIso,
    Continuity.pullbackSectionsEtaleEvaluationIso_inv, Category.assoc, h]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
