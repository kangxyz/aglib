/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeGlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsNaturality
public import Aglib.CategoryTheory.Sites.Point.SectionValues

/-! # The original coefficient-exchange equation on global higher sections

The complete original additive-hom composition is independent of neighborhood
charts. Source and target Ext worlds, all four schemes, and the coefficient
map remain the original ones.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.OriginalSectionValues

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The original higher exchange followed by the original coefficient map is
compatible with the same cohomology pullback as an equality of additive homomorphisms. -/
theorem higherBaseChangeMap_coefficientGlobalSections_hom
    {X S Y T : Scheme.{u}}
    [hDomainExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [hCodomainExt : HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (f : X ⟶ S) (fT : Y ⟶ T) (b : T ⟶ S) (r : Y ⟶ X)
    (h : fT ≫ b = r ≫ f) (F : AbelianSheaf.{u, u + 1} X)
    (G : AbelianSheaf.{u, u + 1} Y) (φ : (inverseImage r).obj F ⟶ G) (q : ℕ) :
    (globalSectionsPullback b ((higherDirectImage f q).obj F) ≫
      (globalSections T).map
        ((higherBaseChangeMap f fT b r h q).app F ≫
          (higherDirectImage fT q).map φ)).hom.comp (cohomologyToHigherSections f F q) =
      (cohomologyToHigherSections fT G q).comp
        ((Sheaf.H.map φ q).comp (cohomologyPullback.{u, w, w'} r F q)) := by
  let Γ : AbelianSheaf.{u, u + 1} T ⥤ AddCommGrpCat.{u + 1} := globalSections T
  let β : (inverseImage b).obj ((higherDirectImage f q).obj F) ⟶
      (higherDirectImage fT q).obj ((inverseImage r).obj F) :=
    (higherBaseChangeMap f fT b r h q).app F
  have hs : (Γ.map β).hom.comp
      ((globalSectionsPullback b ((higherDirectImage f q).obj F)).hom.comp
        (cohomologyToHigherSections f F q)) =
      (cohomologyToHigherSections fT ((inverseImage r).obj F) q).comp
        (cohomologyPullback.{u, w, w'} r F q) :=
    addHom_eq_of_apply _ _
      (@higherBaseChangeMap_cohomologyToHigherSections.{u, w, w'}
        X S Y T hDomainExt hCodomainExt f fT b r h F q)
  have ht : (Γ.map ((higherDirectImage fT q).map φ)).hom.comp
      (cohomologyToHigherSections fT ((inverseImage r).obj F) q) =
      (cohomologyToHigherSections fT G q).comp (Sheaf.H.map φ q) :=
    addHom_eq_of_apply _ _ (cohomologyToHigherSections_naturality fT φ q)
  exact mapped_coefficient_hom Γ β ((higherDirectImage fT q).map φ)
    ((globalSectionsPullback b ((higherDirectImage f q).obj F)).hom.comp
      (cohomologyToHigherSections f F q))
    (cohomologyToHigherSections fT ((inverseImage r).obj F) q)
    (cohomologyToHigherSections fT G q) (cohomologyPullback.{u, w, w'} r F q)
    (Sheaf.H.map φ q) hs ht

end AlgebraicGeometry.Scheme.EtaleCohomology
