/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductGermNaturality

/-! # Original coefficient maps and the higher-image sheafification unit

The original represented classes, original resolution comparison and native
higher-image map commute before passing to stalks. Only the established Shrink
of the original cohomology group appears at the sheafification-unit input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The original unit on a resized original class is the original resolution
comparison followed by the native resolution-to-higher-image map. -/
theorem originalCohomologyToHigherDirectImage_apply_shrink
    (U : S.Etale) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    (originalCohomologyToHigherDirectImage f F q).app (op U)
        (Shrink.addEquiv.{u + 1, w}.symm x) =
      ((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)
        (originalCohomologyResolutionEquiv f U F q x) := by
  let : Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :=
    originalCohomologyPresheaf_small f F q (op U)
  exact congrArg (fun y =>
    ((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)
      (originalCohomologyResolutionEquiv f U F q y))
    (Shrink.addEquiv.{u + 1, w}.apply_symm_apply x)

/-- The original higher-image coefficient map commutes with the actual
sheafification unit on every original represented-cohomology class. -/
theorem originalCohomologyToHigherDirectImage_coefficient
    (U : S.Etale) {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    ((higherDirectImage f q).map g).hom.app (op U)
        ((originalCohomologyToHigherDirectImage f F q).app (op U)
          (Shrink.addEquiv.{u + 1, w}.symm x)) =
      (originalCohomologyToHigherDirectImage f G q).app (op U)
        (Shrink.addEquiv.{u + 1, w}.symm (x.comp (Ext.mk₀ g) (Nat.add_zero q))) := by
  let y := originalCohomologyResolutionEquiv f U F q x
  have hr := originalCohomologyResolutionEquiv_naturality f U g q x
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app ((resolutionCohomologyToHigherDirectImage f q).naturality g)
      (op U)) y
  exact (congrArg (((higherDirectImage f q).map g).hom.app (op U))
    (originalCohomologyToHigherDirectImage_apply_shrink f U F q x)).trans
    (hn.symm.trans ((congrArg (((resolutionCohomologyToHigherDirectImage f q).app G).app
      (op U)) hr.symm).trans
      (originalCohomologyToHigherDirectImage_apply_shrink f U G q
        (x.comp (Ext.mk₀ g) (Nat.add_zero q))).symm))

variable (U : S.Etale)
  [HasExt.{s} (Sheaf ((smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hFibreExt : HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback U.hom f))]

local instance originalPresheafCoefficientFibreExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hFibreExt

/-- The original fibre-product comparison and original higher-image unit retain
arbitrary additive coefficient maps, including Frobenius. -/
theorem fibreProductCohomologyToHigherDirectImage_coefficient
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{e} ((inverseImage (Limits.pullback.snd U.hom f)).obj F) q) :
    ((higherDirectImage f q).map g).hom.app (op U)
        ((originalCohomologyToHigherDirectImage f F q).app (op U)
          (Shrink.addEquiv.{u + 1, w}.symm ((fibreProductCohomologyEquiv f U F q).symm x))) =
      (originalCohomologyToHigherDirectImage f G q).app (op U)
        (Shrink.addEquiv.{u + 1, w}.symm ((fibreProductCohomologyEquiv f U G q).symm
          (Sheaf.H.map ((inverseImage (Limits.pullback.snd U.hom f)).map g) q x))) := by
  let y := (fibreProductCohomologyEquiv f U F q).symm x
  have hn := fibreProductCohomologyEquiv_naturality f U g q y
  let EF := fibreProductCohomologyEquiv f U F q
  let EG := fibreProductCohomologyEquiv f U G q
  have he := (EG.symm_apply_apply (y.comp (Ext.mk₀ g) (Nat.add_zero q))).symm.trans
    ((congrArg EG.symm hn).trans
      (congrArg (fun z => EG.symm
        (Sheaf.H.map ((inverseImage (Limits.pullback.snd U.hom f)).map g) q z))
        (EF.apply_symm_apply x)))
  exact (originalCohomologyToHigherDirectImage_coefficient f U g q y).trans
    (congrArg (fun z => (originalCohomologyToHigherDirectImage f G q).app (op U)
      (Shrink.addEquiv.{u + 1, w}.symm z)) he)

/-- The complete coefficient-value equation on the original unit and inverse
comparison functions. The unit fixes the original resized source and target. -/
def OriginalCohomologyCoefficientValueEquation
    {C D K L : Type*} (k : K → L) (b : L → L) (t : C → D) (r : D → K)
    (x y : C) : Prop :=
  k (r (t y)) = b (k (r (t x)))

/-- Compose the original unit coefficient law, original comparison naturality,
and inverse cancellation before substituting any geometric cohomology group. -/
private theorem originalCoefficientValue_of_equiv
    {C D K L : Type*} (k : K → L) (b : L → L) (E : D ≃ C)
    (r : D → K) (c : C → C) (d : D → D)
    (hk : ∀ z, b (k (r z)) = k (r (d z)))
    (hE : ∀ z, E (d z) = c (E z))
    {x y : C} (hxy : y = c x) :
    OriginalCohomologyCoefficientValueEquation k b E.symm.toFun r x y := by
  subst y
  have ht := (hE (E.symm x)).trans (congrArg c (E.apply_symm_apply x))
  have hi := (congrArg E.symm ht.symm).trans (E.symm_apply_apply (d (E.symm x)))
  exact (congrArg (fun z => k (r z)) hi).trans (hk (E.symm x)).symm

local instance originalPresheafCoefficientValueSmall
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Small.{u + 1} (Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :=
  originalCohomologyPresheaf_small f F q (op U)

/-- The complete original fibre coefficient equation, with its original
functions fixed once before an affine higher-module coefficient is supplied. -/
theorem fibreProductCohomologyToHigherDirectImage_coefficient_values
    {F : AbelianSheaf.{u, u + 1} X} (g : F ⟶ F) (q : ℕ)
    {x y : Sheaf.H.{e} ((inverseImage (Limits.pullback.snd U.hom f)).obj F) q}
    (hxy : y = Sheaf.H.map ((inverseImage (Limits.pullback.snd U.hom f)).map g) q x) :
    OriginalCohomologyCoefficientValueEquation
      ((originalCohomologyToHigherDirectImage f F q).app (op U))
      (((higherDirectImage f q).map g).hom.app (op U))
      (fibreProductCohomologyEquiv.{u, w, s, e} f U
        (hPullbackExt := hFibreExt) F q).symm.toEquiv.toFun
      Shrink.addEquiv.{u + 1, w}.symm.toEquiv.toFun x y := by
  let E := fibreProductCohomologyEquiv.{u, w, s, e} f U
    (hPullbackExt := hFibreExt) F q
  let k := (originalCohomologyToHigherDirectImage f F q).app (op U)
  let b := (((higherDirectImage f q).map g).hom.app (op U))
  let c := Sheaf.H.map ((inverseImage (Limits.pullback.snd U.hom f)).map g) q
  let d (z : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :=
    z.comp (Ext.mk₀ g) (Nat.add_zero q)
  have h := originalCoefficientValue_of_equiv k b E.toEquiv
    Shrink.addEquiv.{u + 1, w}.symm.toEquiv.toFun c d
    (fun z => originalCohomologyToHigherDirectImage_coefficient f U g q z)
    (fun z => fibreProductCohomologyEquiv_naturality f U g q z) hxy
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology
