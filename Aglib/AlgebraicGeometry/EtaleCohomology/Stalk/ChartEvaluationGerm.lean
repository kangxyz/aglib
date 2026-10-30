/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativeUnitGerm
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
  have htest : Continuity.relativeTerminalTest (S := U.left) U.hom U (𝟙 U.left)
      (Category.id_comp U.hom) = Continuity.chartDiagonal U := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (𝟙 U.left) (𝟙 U.left) _ = pullback.diagonal U.hom
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (pullback.diagonal_fst U.hom).symm
    · exact (pullback.lift_snd _ _ _).trans (pullback.diagonal_snd U.hom).symm
  have h := unitSectionMap_relativeTerminalTest_germ (T := U.left) U.hom U (𝟙 U.left)
    (Category.id_comp U.hom) η F (Over.homMk η rfl) (Category.comp_id η).symm p
  rw [Continuity.pullbackSectionsEtaleEvaluationIso_inv]
  dsimp only [Functor.id_obj] at h ⊢
  simpa only [htest, Continuity.unitSectionMap] using h

end AlgebraicGeometry.Scheme.EtaleCohomology
