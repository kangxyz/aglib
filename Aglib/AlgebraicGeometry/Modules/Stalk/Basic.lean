/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Support
/-!
# Module-valued stalks for arbitrary scheme module sheaves

These names specialize the single generic construction for `X.sheaf`. The
actual additive stalk, CommRingCat-stalk action, membership-function skyscraper,
germ maps, and adjunction data are unchanged. No quasicoherence is used.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- A simultaneous representative of a stalk scalar and a module-stalk element. -/
theorem exists_germ_smul_representatives (X : Scheme.{u}) (x : X)
    (M : X.Modules) (r : X.presheaf.stalk x) (m : M.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (s : Γ(M, U)),
      X.presheaf.germ U x hx a = r ∧ M.presheaf.germ U x hx s = m :=
  SheafOfModulesOfCommRing.exists_germ_smul_representatives X.sheaf x M r m

instance instModuleSchemeModuleStalk (X : Scheme.{u}) (x : X) (M : X.Modules) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  SheafOfModulesOfCommRing.instModuleModuleStalk X.sheaf x M

/-- The actual induced map on stalks is linear over the structure-sheaf stalk. -/
abbrev moduleStalkMap {X : Scheme.{u}} (x : X) {M N : X.Modules} (p : M ⟶ N) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
  SheafOfModulesOfCommRing.moduleStalkMap (R := X.sheaf) x p

/-- The stalk functor with its actual module structure. -/
abbrev moduleStalk (X : Scheme.{u}) (x : X) : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  SheafOfModulesOfCommRing.moduleStalk X.sheaf x

instance stalkFunctor_additive (X : Scheme.{u}) (x : X) : (stalkFunctor X x).Additive :=
  SheafOfModulesOfCommRing.stalkFunctor_additive X.sheaf x

/-- Forgetting the module structure gives precisely the established abelian stalk. -/
abbrev moduleStalkForgetIso (X : Scheme.{u}) (x : X) :
    moduleStalk X x ⋙ forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      stalkFunctor X x :=
  SheafOfModulesOfCommRing.moduleStalkForgetIso X.sheaf x

instance moduleStalk_additive (X : Scheme.{u}) (x : X) : (moduleStalk X x).Additive :=
  SheafOfModulesOfCommRing.moduleStalk_additive X.sheaf x

instance stalkFunctor_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (stalkFunctor X x) :=
  SheafOfModulesOfCommRing.stalkFunctor_preservesFiniteLimits X.sheaf x

instance moduleStalk_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (moduleStalk X x) :=
  SheafOfModulesOfCommRing.moduleStalk_preservesFiniteLimits X.sheaf x

/-- Actual module stalks detect monomorphisms of arbitrary module sheaves. -/
theorem mono_of_moduleStalk {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N)
    (hp : ∀ x, Mono ((moduleStalk X x).map p)) : Mono p :=
  SheafOfModulesOfCommRing.mono_of_moduleStalk (R := X.sheaf) p hp

/-- The skyscraper abelian presheaf, written as functions from open membership.
This presentation avoids choices of a zero object on opens missing the point. -/
abbrev pointPresheaf (X : Scheme.{u}) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    TopCat.Presheaf AddCommGrpCat.{u} (X : TopCat.{u}) :=
  SheafOfModulesOfCommRing.pointPresheaf X.sheaf x N

/-- Each skyscraper section is a module over the corresponding ring of sections. -/
instance instModulePointSection (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) :
    Module Γ(X, U) (PLift (x ∈ U) → N) :=
  SheafOfModulesOfCommRing.instModulePointSection X.sheaf x N U

instance instModulePointPresheafObjRingSheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((pointPresheaf X x N).obj U) :=
  SheafOfModulesOfCommRing.instModulePointPresheafObjRingSheaf X.sheaf x N U

instance instModulePointPresheafObjStructureSheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) ((pointPresheaf X x N).obj U) :=
  SheafOfModulesOfCommRing.instModulePointPresheafObjCommRingSheaf X.sheaf x N U

/-- Restriction of a skyscraper section is semilinear for the structure sheaf. -/
theorem pointPresheaf_map_smul (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (r : Γ(X, U.unop)) (s : (pointPresheaf X x N).obj U) :
    (pointPresheaf X x N).map i (r • s) =
      X.presheaf.map i r • (pointPresheaf X x N).map i s :=
  SheafOfModulesOfCommRing.pointPresheaf_map_smul X.sheaf x N i r s

/-- The module skyscraper is an actual sheaf, with arbitrary stalk module. -/
theorem pointPresheaf_isSheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) : (pointPresheaf X x N).IsSheaf :=
  SheafOfModulesOfCommRing.pointPresheaf_isSheaf X.sheaf x N

/-- The actual skyscraper sheaf of modules at a scheme point. -/
abbrev moduleSkyscraperObj (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) : X.Modules :=
  SheafOfModulesOfCommRing.moduleSkyscraperObj X.sheaf x N

/-- Pointwise postcomposition makes the module skyscraper functorial. -/
abbrev moduleSkyscraper (X : Scheme.{u}) (x : X) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.Modules :=
  SheafOfModulesOfCommRing.moduleSkyscraper X.sheaf x

/-- A linear map from the actual module stalk gives a morphism to the skyscraper. -/
abbrev moduleStalkToSkyscraper {X : Scheme.{u}} (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (p : (moduleStalk X x).obj M ⟶ N) :
    M ⟶ (moduleSkyscraper X x).obj N :=
  SheafOfModulesOfCommRing.moduleStalkToSkyscraper (R := X.sheaf) x M N p

/-- The cocone of evaluations of a morphism to a module skyscraper. -/
abbrev moduleSkyscraperCocone {X : Scheme.{u}} (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (p : M ⟶ (moduleSkyscraper X x).obj N) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) :=
  SheafOfModulesOfCommRing.moduleSkyscraperCocone (R := X.sheaf) x M N p

/-- Evaluation of the cocone map on an actual germ. -/
theorem germ_moduleSkyscraperCocone_desc {X : Scheme.{u}} (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (p : M ⟶ (moduleSkyscraper X x).obj N)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) :
    colimit.desc _ (moduleSkyscraperCocone x M N p) (M.presheaf.germ U x hx s) =
      p.app U s ⟨hx⟩ :=
  SheafOfModulesOfCommRing.germ_moduleSkyscraperCocone_desc (R := X.sheaf) x M N p U hx s

/-- A morphism to a module skyscraper induces a linear map from the actual stalk. -/
abbrev moduleSkyscraperFromStalk {X : Scheme.{u}} (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (p : M ⟶ (moduleSkyscraper X x).obj N) :
    (moduleStalk X x).obj M ⟶ N :=
  SheafOfModulesOfCommRing.moduleSkyscraperFromStalk (R := X.sheaf) x M N p

/-- Universal property of the module-valued stalk among module skyscrapers. -/
abbrev moduleStalkSkyscraperHomEquiv (X : Scheme.{u}) (x : X) (M : X.Modules)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    ((moduleStalk X x).obj M ⟶ N) ≃ (M ⟶ (moduleSkyscraper X x).obj N) :=
  SheafOfModulesOfCommRing.moduleStalkSkyscraperHomEquiv X.sheaf x M N

/-- Naturality of the stalk/skyscraper universal property in the sheaf. -/
theorem moduleStalkToSkyscraper_naturality_left {X : Scheme.{u}} (x : X)
    {M M' : X.Modules} (f : M ⟶ M') (N : ModuleCat.{u} (X.presheaf.stalk x))
    (p : (moduleStalk X x).obj M' ⟶ N) :
    moduleStalkToSkyscraper x M N ((moduleStalk X x).map f ≫ p) =
      f ≫ moduleStalkToSkyscraper x M' N p :=
  SheafOfModulesOfCommRing.moduleStalkToSkyscraper_naturality_left (R := X.sheaf) x f N p

/-- The actual module stalk functor is left adjoint to the actual module skyscraper. -/
abbrev moduleStalkSkyscraperAdjunction (X : Scheme.{u}) (x : X) :
    moduleStalk X x ⊣ moduleSkyscraper X x :=
  SheafOfModulesOfCommRing.moduleStalkSkyscraperAdjunction X.sheaf x

instance moduleStalk_isLeftAdjoint (X : Scheme.{u}) (x : X) :
    (moduleStalk X x).IsLeftAdjoint :=
  SheafOfModulesOfCommRing.moduleStalk_isLeftAdjoint X.sheaf x

/-- Module stalks are exact on arbitrary module sheaves. -/
abbrev moduleStalkExactFunctor (X : Scheme.{u}) (x : X) :
    ExactFunctor (sheafExactStructure X)
      (abelianExactStructure (ModuleCat.{u} (X.presheaf.stalk x))) :=
  SheafOfModulesOfCommRing.moduleStalkExactFunctor X.sheaf x

end AlgebraicGeometry.Scheme.Modules
