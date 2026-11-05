/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModulePresheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCoefficientFunctor
public import Aglib.Algebra.Category.ModuleCat.ResizeUnderlying
public import Aglib.CategoryTheory.Preadditive.ScalarDiagramLinear
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantActionNatTrans

/-! # The original resized cohomology as an additive coefficient functor

Only the existing module-valued diagram is resized. The coefficient maps are
its original fibre-cohomology maps. Forgetting scalars recovers the original
small fibre-product coefficient functor, and hence its original abelian
higher-image sheafification. No native module higher-image comparison is
asserted in this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u r w s e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type r) [Ring Λ]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance constantModuleCoefficientFibre_additive (U : S.Etale) (q : ℕ) :
    (constantModuleFibreCohomology.{u, r, e} f Λ U q).Additive := by
  let H := (Functor.whiskeringRight (ModuleCat.{u + 1} Λ)
    AddCommGrpCat.{u + 1} AddCommGrpCat.{e}).obj
      (constantAbelianFibreCohomology f U q)
  let A := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let : (H.obj A).Additive := by
    change (constantModuleFibreCohomologyAb f Λ U q).Additive
    infer_instance
  exact Functor.coefficientModuleDiagram_additive H A
    (ModuleCat.forgetScalarAction Λ)

/-- Every original module coefficient map acts on the same original diagram. -/
def constantModuleCohomologyCoefficientMap {M N : ModuleCat.{u + 1} Λ}
    (a : M ⟶ N) (q : ℕ) :
    constantModuleCohomologyPresheaf f Λ M q ⟶
      constantModuleCohomologyPresheaf f Λ N q where
  app U := (constantModuleFibreCohomology f Λ U.unop q).map a
  naturality _ _ g := (constantModuleFibreRestriction f Λ g.unop q).naturality a |>.symm

local instance constantModuleCoefficientValue_small (M : ModuleCat.{u + 1} Λ) (q : ℕ) :
    ∀ U, Small.{u + 1} ((constantModuleCohomologyPresheaf f Λ M q).obj U) :=
  fun U => fibreProductCohomology_small.{u, w, s, e} f
    ((constantModuleUnderlying (X := X) Λ).obj M) q U.unop

/-- Assemble the original unresized module diagrams in the coefficient variable. -/
def constantModuleCohomologyCoefficientFunctor (q : ℕ) :
    ModuleCat.{u + 1} Λ ⥤ (S.Etaleᵒᵖ ⥤ ModuleCat.{e} Λ) where
  obj M := constantModuleCohomologyPresheaf f Λ M q
  map a := constantModuleCohomologyCoefficientMap f Λ a q
  map_id M := by
    ext U x
    exact ConcreteCategory.congr_hom
      ((constantModuleFibreCohomology f Λ U.unop q).map_id M) x
  map_comp a b := by
    ext U x
    exact ConcreteCategory.congr_hom
      ((constantModuleFibreCohomology f Λ U.unop q).map_comp a b) x

/-- Additivity is the additivity of the original fibre-cohomology maps. -/
instance constantModuleCohomologyCoefficientFunctor_additive (q : ℕ) :
    (constantModuleCohomologyCoefficientFunctor f Λ q).Additive where
  map_add := by
    intro M N a b
    ext U x
    exact ConcreteCategory.congr_hom
      ((constantModuleFibreCohomology f Λ U.unop q).map_add (f := a) (g := b)) x

/-- Reuse original smallness over both coefficient and diagram indices. -/
local instance constantModuleCoefficientFunctorValue_small (q : ℕ) :
    ∀ (M : ModuleCat.{u + 1} Λ) (U : S.Etaleᵒᵖ),
      Small.{u + 1}
        (((constantModuleCohomologyCoefficientFunctor f Λ q).obj M).obj U) :=
  fun M U => fibreProductCohomology_small.{u, w, s, e} f
    ((constantModuleUnderlying (X := X) Λ).obj M) q U.unop

/-- Forgetting scalars retains the same original small cohomology carrier. -/
local instance constantModuleCoefficientUnderlyingValue_small (M : ModuleCat.{u + 1} Λ) (q : ℕ) :
    ∀ U, Small.{u + 1}
      ((constantModuleCohomologyPresheaf f Λ M q ⋙
        forget₂ (ModuleCat.{e} Λ) AddCommGrpCat.{e}).obj U) :=
  fun U => fibreProductCohomology_small.{u, w, s, e} f
    ((constantModuleUnderlying (X := X) Λ).obj M) q U.unop

/-- Apply the general resize to the actual original coefficient diagram. -/
def smallConstantModuleCohomologyFunctor (q : ℕ) :
    ModuleCat.{u + 1} Λ ⥤ (S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :=
  ModuleCat.resizeDiagramFunctor.{u + 1} Λ
    (constantModuleCohomologyCoefficientFunctor f Λ q)

/-- The generic resize preserves additivity of the original coefficient maps. -/
instance smallConstantModuleCohomologyFunctor_additive (q : ℕ) :
    (smallConstantModuleCohomologyFunctor f Λ q).Additive := by
  unfold smallConstantModuleCohomologyFunctor
  infer_instance

/-- Reuse the original smallness family without changing its coefficient maps. -/
local instance constantModuleCoefficientOriginalFunctorValue_small (q : ℕ) :
    ∀ (F : AbelianSheaf.{u, u + 1} X) (U : S.Etaleᵒᵖ),
      Small.{u + 1}
        (((Stalk.originalFibreProductCohomologyFunctor.{u, w, s, e} f q).obj F).obj U) :=
  fun F U => fibreProductCohomology_small.{u, w, s, e} f F q U.unop

/-- Forgetting the module action recovers the same original coefficient diagram. -/
def smallConstantModuleCohomologyUnderlyingIso (q : ℕ) :
    smallConstantModuleCohomologyFunctor f Λ q ⋙
        (Functor.whiskeringRight S.Etaleᵒᵖ _ _).obj
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      constantModuleUnderlying (X := X) Λ ⋙ smallFibreProductCohomologyFunctor f q :=
  ModuleCat.resizeDiagramFunctorUnderlyingIsoOfAddEquiv.{u + 1} Λ
    (constantModuleCohomologyCoefficientFunctor f Λ q)
    (constantModuleUnderlying (X := X) Λ)
    (Stalk.originalFibreProductCohomologyFunctor.{u, w, s, e} f q)
    (fun _ _ => AddEquiv.refl _) (by intros; rfl) (by intros; rfl)

/-- Original module cohomology sheafification as a coefficient functor. -/
abbrev constantModuleCohomologySheafificationFunctor (q : ℕ) :
    ModuleCat.{u + 1} Λ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  smallConstantModuleCohomologyFunctor f Λ q ⋙
    presheafToSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)

/-- Forgetting scalars gives the original higher direct image by its existing
coefficient-natural sheafification isomorphism, with the same native maps. -/
def constantModuleCohomologySheafificationUnderlyingIso (q : ℕ) :
    constantModuleCohomologySheafificationFunctor f Λ q ⋙
        ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology ≅
      constantModuleUnderlying (X := X) Λ ⋙ higherDirectImage f q := by
  letI : S.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.Sheaf.forget_preservesSheafification Λ S.smallEtaleTopology
  exact Functor.isoWhiskerLeft (smallConstantModuleCohomologyFunctor f Λ q)
      (sheafComposeNatIso S.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
        (sheafificationAdjunction S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1})).symm ≪≫
    Functor.isoWhiskerRight (smallConstantModuleCohomologyUnderlyingIso f Λ q)
      (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) ≪≫
    Functor.isoWhiskerLeft (constantModuleUnderlying (X := X) Λ)
      (fibreProductCohomologySheafificationNatIso f q)

end AlgebraicGeometry.Scheme.EtaleCohomology
