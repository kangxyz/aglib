/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackRestrictionSections

/-! # Scalar normalization of original relative section transport -/
@[expose] public noncomputable section
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- The original chart evaluation and original coefficient comparison as one transport. -/
def pullbackSectionTransport {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (W : S.Etale) :
    ((inverseImage f).obj F).obj.obj (op W) ⟶
      (globalSections W.left).obj ((inverseImage (W.hom ≫ f)).obj F) :=
  (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv ≫
    (globalSections W.left).map ((inverseImageComp f W.hom).inv.app F)

instance {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (W : S.Etale) :
    IsIso (pullbackSectionTransport f F W) := by
  unfold pullbackSectionTransport
  infer_instance

/-- The original unit normalization with its intermediate transport kept opaque. -/
theorem unitSectionMap_transport {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale} {W : S.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) :
    unitSectionMap f F a ≫ pullbackSectionTransport f F W =
      (pullbackSectionsEtaleEvaluationIso F U).inv ≫
        pullbackSectionsMap F (unitRepresentativeArrow f a) :=
  unitSectionMap_etaleEvaluation f F a

/-- Scalar form of the original unit normalization. -/
theorem pullbackSectionTransport_unit {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale} {W : S.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) (t : F.obj.obj (op U)) :
    pullbackSectionTransport f F W (unitSectionMap f F a t) =
      ((pullbackSectionsEtaleEvaluationIso F U).inv ≫
        pullbackSectionsMap F (unitRepresentativeArrow f a)) t :=
  (ConcreteCategory.comp_apply (unitSectionMap f F a)
    (pullbackSectionTransport f F W) t).symm.trans
      (ConcreteCategory.congr_hom (unitSectionMap_transport f F a) t)

/-- The original restriction normalization with its intermediate transport kept opaque. -/
theorem pullbackRestriction_transport {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (W : S.Etale) (g : W ⟶ etaleTerminal S) :
    ((inverseImage f).obj F).obj.map g.op ≫ pullbackSectionTransport f F W =
      pullbackSectionsMap F
        (Over.homMk W.hom (U := Over.mk (W.hom ≫ f)) (V := Over.mk f)) :=
  pullbackRestriction_evaluation_inv f F W g

/-- Scalar form of the original restriction normalization. -/
theorem pullbackSectionTransport_restriction {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (W : S.Etale) (g : W ⟶ etaleTerminal S)
    (s : (globalSections S).obj ((inverseImage f).obj F)) :
    pullbackSectionTransport f F W (((inverseImage f).obj F).obj.map g.op s) =
      pullbackSectionsMap F
        (Over.homMk W.hom (U := Over.mk (W.hom ≫ f)) (V := Over.mk f)) s :=
  (ConcreteCategory.comp_apply (((inverseImage f).obj F).obj.map g.op)
    (pullbackSectionTransport f F W) s).symm.trans
      (ConcreteCategory.congr_hom (pullbackRestriction_transport f F W g) s)

/-- The canonical functor map is the original relative section morphism. -/
theorem pullbackSectionsFunctor_map {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    {Y Z : Over X} (a : Y ⟶ Z) :
    (pullbackSectionsFunctor F).map a.op = pullbackSectionsMap F a := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
