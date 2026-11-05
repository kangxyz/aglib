/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.ResizeNaturality
public import Aglib.Algebra.Category.Grp.DiagramValueNaturality
public import Aglib.CategoryTheory.Adjunction.UnitComparison
public import Aglib.CategoryTheory.NatTrans.ComponentFactorization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalPresheafCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalResolutionValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCoefficientFunctor.Maps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCoefficientFunctor.Values

/-!
# Coefficient functoriality of original fibre-product cohomology

The existing small fibre-product cohomology presheaves form an additive
functor in the original abelian coefficient. Its objects are unchanged;
coefficient maps are the original inverse-image cohomology maps resized by
the same group equivalences. The original sheafification isomorphisms are
natural for these maps and retain the original whole sheafification unit.
Source, slice and fibre-product Ext universes remain independent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (q : ℕ)

/-- Assemble the two original comparisons before applying the higher-image unit. -/
def fibreProductCohomologyResolutionNatTrans :
    smallFibreProductCohomologyFunctor f q ⟶ resolutionCohomologyPresheaf f q :=
  additiveDiagramNatTransOfTwoComparisons
    (smallFibreProductCohomologyFunctor f q) (resolutionCohomologyPresheaf f q)
    (fun F => smallOriginalCohomologyPresheaf f F q)
    (fun F U => Sheaf.H.{e} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q)
    (fun F U => Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (smallEtaleTopology X) F q ((siteBaseChange f).obj U.unop))
    (fun F U => (Shrink.addEquiv.{u + 1, e}
      (α := Sheaf.H.{e} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q)).symm)
    (fun F U => (Shrink.addEquiv.{u + 1, w}
      (α := (originalCohomologyPresheaf.{u, w} f F q).obj U)).symm)
    (fun F U => (Shrink.addEquiv.{u + 1, e}
      (α := Sheaf.H.{e} ((inverseImage (pullback.snd U.unop.hom f)).obj F) q)).symm.surjective)
    (fun {_ _} g U x =>
      Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map g) q x)
    (fun {_ _} g U y => ((resolutionCohomologyPresheaf f q).map g).app U y)
    (fun {_ _} g _ y => y.comp (CategoryTheory.Abelian.Ext.mk₀ g) (Nat.add_zero q))
    (fun {_ _} g U x =>
      smallFibreProductCohomologyCoefficientMap_app_shrink.{u, w, s, e} f q g U.unop x)
    (fun {_ _} _ _ _ => rfl)
    (fun F => (smallFibreProductOriginalIso f F q).hom)
    (fun F => (smallOriginalCohomologyResolutionIso f F q).hom)
    (fun F U => (fibreProductCohomologyEquiv.{u, w, s, e} f U.unop F q).symm)
    (fun F U => originalCohomologyResolutionEquiv f U.unop F q)
    (fun F U x => smallFibreProductOriginalIso_apply_shrink.{u, w, s, e} f q F U.unop x)
    (fun F U x => smallOriginalCohomologyResolutionIso_apply_shrink f F q U.unop x)
    (fun {_ _} g U x =>
      fibreProductCohomologyEquiv_symm_coefficient.{u, w, s, e} f q g U.unop x)
    (fun {_ _} g U x => originalCohomologyResolutionEquiv_naturality f U.unop g q x)

/-- The original higher-image unit is natural by its original resolution factorization. -/
def fibreProductCohomologyToHigherDirectImageNatTrans :
    smallFibreProductCohomologyFunctor f q ⟶
      higherDirectImage f q ⋙ sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  natTransOfComponentFactorization (fibreProductCohomologyResolutionNatTrans f q)
    (resolutionCohomologyToHigherDirectImage f q)
    (fun F => fibreProductCohomologyToHigherDirectImage f F q) (by
      intro F
      change (smallFibreProductOriginalIso f F q).hom ≫
          ((smallOriginalCohomologyResolutionIso f F q).hom ≫
            (resolutionCohomologyToHigherDirectImage f q).app F) =
        ((smallFibreProductOriginalIso f F q).hom ≫
          (smallOriginalCohomologyResolutionIso f F q).hom) ≫
            (resolutionCohomologyToHigherDirectImage f q).app F
      exact (Category.assoc _ _ _).symm)

/-- The existing sheafification isomorphisms commute with all original coefficient maps. -/
theorem fibreProductCohomologySheafificationIso_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) :
    (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((smallFibreProductCohomologyFunctor f q).map g) ≫
        (fibreProductCohomologySheafificationIso f G q).hom =
      (fibreProductCohomologySheafificationIso f F q).hom ≫
        (higherDirectImage f q).map g :=
  Adjunction.comparison_naturality_of_unit
    (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (smallFibreProductCohomologyFunctor f q) (higherDirectImage f q)
    (fibreProductCohomologyToHigherDirectImageNatTrans f q)
    (fun F => fibreProductCohomologySheafificationIso f F q)
    (fun F => fibreProductCohomologyToHigherDirectImage_unit f F q) g

/-- Sheafifying the original coefficient functor gives the original higher direct image. -/
def fibreProductCohomologySheafificationNatIso :
    smallFibreProductCohomologyFunctor f q ⋙
        presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      higherDirectImage f q :=
  Adjunction.comparisonNatIsoOfUnit
    (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (smallFibreProductCohomologyFunctor f q) (higherDirectImage f q)
    (fibreProductCohomologyToHigherDirectImageNatTrans f q)
    (fun F => fibreProductCohomologySheafificationIso f F q)
    (fun F => fibreProductCohomologyToHigherDirectImage_unit f F q)

/-- The complete natural comparison retains the same original sheafification unit. -/
theorem fibreProductCohomologySheafificationNatIso_unit :
    (Functor.rightUnitor (smallFibreProductCohomologyFunctor f q)).inv ≫
      Functor.whiskerLeft (smallFibreProductCohomologyFunctor f q)
        (toSheafification S.smallEtaleTopology AddCommGrpCat.{u + 1}) ≫
      (Functor.associator (smallFibreProductCohomologyFunctor f q)
        (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
        (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})).inv ≫
      Functor.whiskerRight (fibreProductCohomologySheafificationNatIso f q).hom
        (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) =
      fibreProductCohomologyToHigherDirectImageNatTrans f q :=
  Adjunction.comparisonNatIsoOfUnit_unit
    (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (smallFibreProductCohomologyFunctor f q) (higherDirectImage f q)
    (fibreProductCohomologyToHigherDirectImageNatTrans f q)
    (fun F => fibreProductCohomologySheafificationIso f F q)
    (fun F => fibreProductCohomologyToHigherDirectImage_unit f F q)

end AlgebraicGeometry.Scheme.EtaleCohomology
