/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.ResizeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalPresheafCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalResolutionValues

/-! # Values of the original fibre-product and resolution comparisons -/

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

/-- The existing fibre-product unit retains the original represented-cohomology value. -/
theorem fibreProductCohomologyToHigherDirectImage_apply_shrink
    (F : AbelianSheaf.{u, u + 1} X) (U : S.Etale)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (fibreProductCohomologyToHigherDirectImage f F q).app (op U)
        (Shrink.addEquiv.{u + 1, e}.symm x) =
      (originalCohomologyToHigherDirectImage f F q).app (op U)
        (Shrink.addEquiv.{u + 1, w}.symm
          ((fibreProductCohomologyEquiv.{u, w, s, e} f U F q).symm x)) := by
  change (originalCohomologyToHigherDirectImage f F q).app (op U)
      ((smallFibreProductOriginalIso f F q).hom.app (op U)
        (Shrink.addEquiv.{u + 1, e}.symm x)) = _
  apply congrArg ((originalCohomologyToHigherDirectImage f F q).app (op U))
  exact resizeAdditiveDiagramIsoOfAddEquiv_hom_app_shrink.{u + 1, e, w}
    (P := Stalk.originalFibreProductCohomologyPresheaf.{u, w, s, e} f F q)
    (Q := originalCohomologyPresheaf.{u, w} f F q)
    (fun V => (fibreProductCohomologyEquiv.{u, w, s, e} f V.unop F q).symm)
    (fun {V W} (a : V ⟶ W) y =>
      fibreProductCohomologyRestriction_original f F q a.unop y) (op U) x

/-- The original fibre-product unit commutes with coefficients on every original class. -/
theorem fibreProductCohomologyToHigherDirectImage_coefficient_shrink
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (U : S.Etale)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (fibreProductCohomologyToHigherDirectImage f G q).app (op U)
        (Shrink.addEquiv.{u + 1, e}.symm
          (Sheaf.H.map ((inverseImage (pullback.snd U.hom f)).map g) q x)) =
      (((higherDirectImage f q).map g).hom.app (op U))
        ((fibreProductCohomologyToHigherDirectImage f F q).app (op U)
          (Shrink.addEquiv.{u + 1, e}.symm x)) := by
  have hF := fibreProductCohomologyToHigherDirectImage_apply_shrink.{u, w, s, e}
    f q F U x
  have hG := fibreProductCohomologyToHigherDirectImage_apply_shrink.{u, w, s, e}
    f q G U (Sheaf.H.map ((inverseImage (pullback.snd U.hom f)).map g) q x)
  have hc := fibreProductCohomologyToHigherDirectImage_coefficient.{u, w, s, e}
    f U g q x
  exact hG.trans (hc.symm.trans
    (congrArg (((higherDirectImage f q).map g).hom.app (op U)) hF.symm))

/-- The unchanged composite comparison with the original resolution diagram. -/
def fibreProductCohomologyResolutionIso (F : AbelianSheaf.{u, u + 1} X) :
    smallFibreProductCohomologyPresheaf f F q ≅
      (resolutionCohomologyPresheaf f q).obj F :=
  smallFibreProductOriginalIso f F q ≪≫ smallOriginalCohomologyResolutionIso f F q

/-- The existing first comparison retains its original Shrink values. -/
theorem smallFibreProductOriginalIso_apply_shrink
    (F : AbelianSheaf.{u, u + 1} X) (U : S.Etale)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (smallFibreProductOriginalIso f F q).hom.app (op U)
        (Shrink.addEquiv.{u + 1, e}.symm x) =
      (Shrink.addEquiv.{u + 1, w}
        (α := (originalCohomologyPresheaf.{u, w} f F q).obj (op U))).symm
        ((fibreProductCohomologyEquiv.{u, w, s, e} f U F q).symm x) :=
  resizeAdditiveDiagramIsoOfAddEquiv_hom_app_shrink.{u + 1, e, w}
    (P := Stalk.originalFibreProductCohomologyPresheaf.{u, w, s, e} f F q)
    (Q := originalCohomologyPresheaf.{u, w} f F q)
    (fun V => (fibreProductCohomologyEquiv.{u, w, s, e} f V.unop F q).symm)
    (fun {V W} (a : V ⟶ W) y =>
      fibreProductCohomologyRestriction_original f F q a.unop y) (op U) x

/-- Inverse comparison compatibility on original classes, without either unit map. -/
theorem fibreProductCohomologyEquiv_symm_coefficient
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (U : S.Etale)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (fibreProductCohomologyEquiv.{u, w, s, e} f U G q).symm
        (Sheaf.H.map ((inverseImage (pullback.snd U.hom f)).map g) q x) =
      ((fibreProductCohomologyEquiv.{u, w, s, e} f U F q).symm x).comp
        (CategoryTheory.Abelian.Ext.mk₀ g) (Nat.add_zero q) := by
  let EF := fibreProductCohomologyEquiv.{u, w, s, e} f U F q
  let EG := fibreProductCohomologyEquiv.{u, w, s, e} f U G q
  let y := EF.symm x
  have hn := fibreProductCohomologyEquiv_naturality.{u, w, s, e} f U g q y
  exact ((EG.symm_apply_apply
      (y.comp (CategoryTheory.Abelian.Ext.mk₀ g) (Nat.add_zero q))).symm.trans
    ((congrArg EG.symm hn).trans
      (congrArg (fun z => EG.symm
        (Sheaf.H.map ((inverseImage (pullback.snd U.hom f)).map g) q z))
        (EF.apply_symm_apply x)))).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
