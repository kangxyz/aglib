/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestrictionCoefficients
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars
public import Aglib.CategoryTheory.Preadditive.ScalarDiagramTransform
public import Aglib.Algebra.Category.ModuleCat.ForgetAction

/-! # Original constant-module fibre-product cohomology presheaves

The coefficient action is the image of the original scalar endomorphism under
original cohomology. Restrictions are the existing fibre-product restriction
maps. Naturality in coefficients makes those maps linear, without identifying
unrelated actions on equal additive carriers. No higher-image scalar comparison
or constructibility statement is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u r w s e e'

attribute [local instance] hasSheafifyLarge

section Values

variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type r) [Ring Λ]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- The original constant abelian coefficient of a module. -/
abbrev constantModuleUnderlying : ModuleCat.{u + 1} Λ ⥤ AbelianSheaf.{u, u + 1} X :=
  forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ⋙
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}

/-- The actual cohomology of the pulled-back constant coefficient at a test. -/
abbrev constantModuleFibreCohomologyAb (U : S.Etale) (q : ℕ) :
    ModuleCat.{u + 1} Λ ⥤ AddCommGrpCat.{e} :=
  constantModuleUnderlying (X := X) Λ ⋙ inverseImage (pullback.snd U.hom f) ⋙
    Sheaf.functorH (pullback U.hom f).smallEtaleTopology q

omit [Ring Λ] in
/-- The whole original additive coefficient functor, before scalar enrichment. -/
abbrev constantAbelianFibreCohomology (U : S.Etale) (q : ℕ) :
    AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{e} :=
  constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    inverseImage (pullback.snd U.hom f) ⋙
      Sheaf.functorH (pullback U.hom f).smallEtaleTopology q

/-- Scalar enrichment leaves every original cohomology carrier unchanged. -/
def constantModuleFibreCohomology (U : S.Etale) (q : ℕ) :
    ModuleCat.{u + 1} Λ ⥤ ModuleCat.{e} Λ :=
  ((Functor.whiskeringRight (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1} AddCommGrpCat.{e}).obj
        (constantAbelianFibreCohomology f U q)).coefficientModuleDiagram
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (ModuleCat.forgetScalarAction Λ)

/-- The original restriction is a natural transformation in the coefficient. -/
def constantModuleFibreRestrictionAb {U V : S.Etale} (g : V ⟶ U) (q : ℕ) :
    constantModuleFibreCohomologyAb f Λ U q ⟶
      constantModuleFibreCohomologyAb f Λ V q where
  app M := AddCommGrpCat.ofHom
    (fibreProductCohomologyRestriction f g
      ((constantModuleUnderlying (X := X) Λ).obj M) q)
  naturality M N a := by
    ext x
    exact fibreProductCohomologyRestriction_coefficientMap f g
      ((constantModuleUnderlying (X := X) Λ).map a) q x

omit [Ring Λ] in
/-- Restriction is natural on the entire original additive coefficient category. -/
def constantAbelianFibreRestriction {U V : S.Etale} (g : V ⟶ U) (q : ℕ) :
    constantAbelianFibreCohomology f U q ⟶ constantAbelianFibreCohomology f V q where
  app M := AddCommGrpCat.ofHom
    (fibreProductCohomologyRestriction f g
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q)
  naturality M N a := by
    ext x
    exact fibreProductCohomologyRestriction_coefficientMap f g
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map a) q x

/-- The unchanged restriction is linear for the true whole-functor scalar action. -/
def constantModuleFibreRestriction {U V : S.Etale} (g : V ⟶ U) (q : ℕ) :
    constantModuleFibreCohomology f Λ U q ⟶
      constantModuleFibreCohomology f Λ V q :=
  Functor.coefficientModuleDiagramNatTrans
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (ModuleCat.forgetScalarAction Λ)
    ((Functor.whiskeringRight (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1} AddCommGrpCat.{e}).map
        (constantAbelianFibreRestriction f g q))

/-- Forgetting scalars does not change the restriction function. -/
theorem constantModuleFibreRestriction_apply {U V : S.Etale} (g : V ⟶ U)
    (q : ℕ) (M : ModuleCat.{u + 1} Λ)
    (x : (constantModuleFibreCohomology f Λ U q).obj M) :
    (constantModuleFibreRestriction f Λ g q).app M x =
      fibreProductCohomologyRestriction f g
        ((constantModuleUnderlying (X := X) Λ).obj M) q x := rfl

end Values

section Presheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type r) [Ring Λ]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- The original unresized fibre-product cohomology diagram with its canonical
constant-coefficient scalars. All test and coefficient maps are the original ones. -/
def constantModuleCohomologyPresheaf (M : ModuleCat.{u + 1} Λ) (q : ℕ) :
    S.Etaleᵒᵖ ⥤ ModuleCat.{e} Λ where
  obj U := (constantModuleFibreCohomology f Λ U.unop q).obj M
  map g := (constantModuleFibreRestriction f Λ g.unop q).app M
  map_id U := by
    ext x
    exact fibreProductCohomologyRestriction_id f
      ((constantModuleUnderlying (X := X) Λ).obj M) q U.unop x
  map_comp g h := by
    ext x
    exact fibreProductCohomologyRestriction_comp f
      ((constantModuleUnderlying (X := X) Λ).obj M) q g.unop h.unop x

/-- The underlying additive diagram is precisely the existing original
fibre-product diagram, not a second cohomology realization. -/
def constantModuleCohomologyPresheafUnderlyingIso
    (M : ModuleCat.{u + 1} Λ) (q : ℕ) :
    constantModuleCohomologyPresheaf f Λ M q ⋙
        forget₂ (ModuleCat.{e} Λ) AddCommGrpCat.{e} ≅
      Stalk.originalFibreProductCohomologyPresheaf f
        ((constantModuleUnderlying (X := X) Λ).obj M) q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V g
    ext x
    rfl)

end Presheaf

end AlgebraicGeometry.Scheme.EtaleCohomology
