/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackScalarTransport

/-! # Original unit equality detected by original relative representatives -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private theorem representative_section_apply {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (Y : Over X) (U : X.Etale)
    (a : Y ⟶ (Etale.forget X).obj U) (t : F.obj.obj (op U)) :
    ((pullbackSectionsEtaleEvaluationIso F U).inv ≫ pullbackSectionsMap F a) t =
      etaleRepresentativeSection F Y U a t := by
  change ((pullbackSectionsEtaleEvaluationIso F U).inv ≫
    (pullbackSectionsFunctor F).map a.op) t = _
  exact ConcreteCategory.comp_apply _ _ _

private theorem unitSectionMap_eq_iff_composite_eq
    {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (W : S.Etale) (U V : X.Etale)
    (a : W ⟶ (siteBaseChange f).obj U) (b : W ⟶ (siteBaseChange f).obj V)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V)) :
    unitSectionMap f F a s = unitSectionMap f F b t ↔
      ((pullbackSectionsEtaleEvaluationIso F U).inv ≫
        pullbackSectionsMap F (unitRepresentativeArrow f a)) s =
      ((pullbackSectionsEtaleEvaluationIso F V).inv ≫
        pullbackSectionsMap F (unitRepresentativeArrow f b)) t := by
  have hs := pullbackSectionTransport_unit f F a s
  have ht := pullbackSectionTransport_unit f F b t
  constructor
  · intro h
    exact hs.symm.trans ((congrArg (pullbackSectionTransport f F W) h).trans ht)
  · intro h
    exact (ConcreteCategory.bijective_of_isIso
      (pullbackSectionTransport f F W)).injective (hs.trans (h.trans ht.symm))

/-- Equality of original inverse-image unit sections is equivalent to equality
of their original relative representatives. This is the matching-family bridge
used before applying the original inverse-image sheaf axiom. -/
theorem unitSectionMap_eq_iff_representative_eq
    {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (W : S.Etale) (U V : X.Etale)
    (a : W ⟶ (siteBaseChange f).obj U) (b : W ⟶ (siteBaseChange f).obj V)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V)) :
    unitSectionMap f F a s = unitSectionMap f F b t ↔
      etaleRepresentativeSection F (Over.mk (W.hom ≫ f)) U
        (unitRepresentativeArrow f a) s =
      etaleRepresentativeSection F (Over.mk (W.hom ≫ f)) V
        (unitRepresentativeArrow f b) t := by
  exact (unitSectionMap_eq_iff_composite_eq f F W U V a b s t).trans
    (congrArg₂ Eq
      (representative_section_apply F _ U (unitRepresentativeArrow f a) s)
      (representative_section_apply F _ V (unitRepresentativeArrow f b) t)).to_iff

/-- Restricting an original unit representative composes its actual test map. -/
theorem unitSectionMap_precomp {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale} {W Z : S.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) (g : Z ⟶ W) :
    unitSectionMap f F a ≫ ((inverseImage f).obj F).obj.map g.op =
      unitSectionMap f F (g ≫ a) := by
  simp only [unitSectionMap, op_comp, Functor.map_comp]
  exact Category.assoc _ _ _

end AlgebraicGeometry.Scheme.EtaleAffineBasis
