/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartCoefficientNaturality

/-! # Coefficient naturality of original fibre-product cohomology germs

The native higher-image stalk map commutes with the original inverse-image
coefficient map on the actual fibre-product scheme. The three Ext universes
remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The canonical original value comparison respects original coefficient maps. -/
theorem originalCohomologyResolutionEquiv_naturality (U : S.Etale)
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    originalCohomologyResolutionEquiv f U G q
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero q)) =
      ((resolutionCohomologyPresheaf f q).map g).app (op U)
        (originalCohomologyResolutionEquiv f U F q x) := by
  let φ : InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) g :=
    ⟨InjectiveResolution.desc g _ _,
      HomologicalComplex.congr_hom
        (InjectiveResolution.desc_commutes g (injectiveResolution G)
          (injectiveResolution F)) 0⟩
  exact originalCohomologyResolutionEquivOfResolution_naturality f U φ q x

/-- Original Ext germs commute with the native higher-image stalk coefficient map. -/
theorem originalCohomologyGerm_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (U : S.Etale) (p : (pointSmallEtale η).fiber.obj U)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((higherDirectImage f q).map g) (originalCohomologyGerm f F q η U p x) =
      originalCohomologyGerm f G q η U p
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero q)) := by
  let y := originalCohomologyResolutionEquiv f U F q x
  have hresolution := originalCohomologyResolutionEquiv_naturality f U g q x
  have hcomparison := ConcreteCategory.congr_hom
    (NatTrans.congr_app ((resolutionCohomologyToHigherDirectImage f q).naturality g)
      (op U)) y
  have hgerm := ConcreteCategory.congr_hom
    ((pointSmallEtale η).toPresheafFiber_naturality
      (((higherDirectImage f q).map g).hom) U p)
    ((((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)) y)
  change _ = (pointSmallEtale η).toPresheafFiber U p
    ((higherDirectImage f q).obj G).obj
    ((((resolutionCohomologyToHigherDirectImage f q).app G).app (op U))
      (originalCohomologyResolutionEquiv f U G q
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero q))))
  rw [hresolution]
  exact hgerm.trans (congrArg
    ((pointSmallEtale η).toPresheafFiber U p ((higherDirectImage f q).obj G).obj)
    hcomparison.symm)

variable (U : S.Etale)
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [hFibreProductGermExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance fibreProductGermNaturalityChartExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) :=
  hFibreProductGermExt

/-- The actual fibre-product value comparison respects original coefficient maps. -/
theorem fibreProductCohomologyEquiv_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    fibreProductCohomologyEquiv f U G q
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero q)) =
      Sheaf.H.map ((inverseImage (pullback.snd U.hom f)).map g) q
        (fibreProductCohomologyEquiv f U F q x) :=
  originalCohomologyChartEquiv_naturality ((siteBaseChange f).obj U) g q x

/-- Coefficient naturality on the original scheme cohomology and native stalk. -/
theorem fibreProductCohomologyGerm_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)
    (p : (pointSmallEtale η).fiber.obj U)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((higherDirectImage f q).map g) (fibreProductCohomologyGerm f U F q η p x) =
      fibreProductCohomologyGerm f U G q η p
        (Sheaf.H.map ((inverseImage (pullback.snd U.hom f)).map g) q x) := by
  obtain ⟨y, rfl⟩ := (fibreProductCohomologyEquiv f U F q).surjective x
  rw [← fibreProductCohomologyEquiv_naturality f U g q y]
  change ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((higherDirectImage f q).map g)
      (originalCohomologyGerm f F q η U p
        ((fibreProductCohomologyEquiv f U F q).symm
          (fibreProductCohomologyEquiv f U F q y))) =
    originalCohomologyGerm f G q η U p
      ((fibreProductCohomologyEquiv f U G q).symm
        (fibreProductCohomologyEquiv f U G q
          (y.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero q))))
  exact (congrArg
    (fun z => ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((higherDirectImage f q).map g) (originalCohomologyGerm f F q η U p z))
    ((fibreProductCohomologyEquiv f U F q).symm_apply_apply y)).trans
      ((originalCohomologyGerm_naturality f g q η U p y).trans
        (congrArg (originalCohomologyGerm f G q η U p)
          ((fibreProductCohomologyEquiv f U G q).symm_apply_apply
            (y.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero q))).symm))

end AlgebraicGeometry.Scheme.EtaleCohomology
