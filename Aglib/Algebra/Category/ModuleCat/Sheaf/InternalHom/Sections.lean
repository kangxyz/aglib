/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Additive
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Original internal-Hom sections and injective slice targets

The existing section comparison is additive and natural in both original
coefficients. As a whole natural isomorphism, it compares evaluation of internal
Hom with the native slice Hom functor. Injectivity of the actual restricted
target gives surjectivity of the original source-precomposition section map.
The sectionwise statement also gives an epimorphism of the original sheaves.
No injectivity of stalks or exactness of tensor is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r m

namespace SheafOfModules.InternalHom

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (R : Sheaf J CommRingCat.{r})
  (M N : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- The original section-to-slice-morphism comparison preserves addition. -/
def sectionHomAddEquiv (U : C) :
    (sheaf R M N).val.obj (op U) ≃+ (M.over U ⟶ N.over U) where
  __ := sectionHomEquiv R M N U
  map_add' s t := by
    ext V x
    rfl

/-- Both original coefficient maps agree with precomposition and postcomposition on the slice. -/
theorem sectionHomAddEquiv_map
    {M' N' : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M' ⟶ M) (b : N ⟶ N') (U : C) (s : (sheaf R M N).val.obj (op U)) :
    sectionHomAddEquiv R M' N' U ((map R a b).val.app (op U) s) =
      (SheafOfModules.overFunctor _ U).map a ≫ sectionHomAddEquiv R M N U s ≫
        (SheafOfModules.overFunctor _ U).map b := by
  exact (sectionHomEquiv R M' N' U).apply_symm_apply _

/-- Restriction retains the original native over-functor comparison on both coefficients. -/
theorem sectionHomAddEquiv_restrict {U V : Cᵒᵖ} (i : U ⟶ V)
    (s : (sheaf R M N).val.obj U) :
    sectionHomAddEquiv R M N V.unop ((sheaf R M N).val.map i s) =
      (SheafOfModules.overFunctorMap _ i.unop).inv.app M ≫
        (SheafOfModules.overMap _ i.unop).map (sectionHomAddEquiv R M N U.unop s) ≫
        (SheafOfModules.overFunctorMap _ i.unop).hom.app N :=
  sectionHomEquiv_map R M N i s

variable {M}

/-- A monomorphism on the actual slice induces a surjective section map into an injective. -/
theorem precompose_sections_surjective
    {M' : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M' ⟶ M) (U : C)
    [Mono ((SheafOfModules.overFunctor _ U).map a)] [Injective (N.over U)] :
    Function.Surjective ((map R a (𝟙 N)).val.app (op U)) := by
  intro s
  refine ⟨(sectionHomAddEquiv R M N U).symm
    (Injective.factorThru (sectionHomAddEquiv R M' N U s)
      ((SheafOfModules.overFunctor _ U).map a)), ?_⟩
  apply (sectionHomAddEquiv R M' N U).injective
  rw [sectionHomAddEquiv_map, AddEquiv.apply_symm_apply, CategoryTheory.Functor.map_id,
    Category.comp_id, Injective.comp_factorThru]

/-- Sectionwise injectivity of the restricted target gives the original sheaf epimorphism. -/
theorem precompose_epi_of_injective_over
    {M' : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : M' ⟶ M) [∀ U : C, Mono ((SheafOfModules.overFunctor _ U).map a)]
    [∀ U : C, Injective (N.over U)] : Epi (map R a (𝟙 N)) := by
  have h : Epi (map R a (𝟙 N)).val := PresheafOfModules.epi_of_surjective
    (fun {U} => precompose_sections_surjective R N a U.unop)
  exact (SheafOfModules.forget _).epi_of_epi_map h

end SheafOfModules.InternalHom

namespace SheafOfModules.InternalHom

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})]
  (R : Sheaf J CommRingCat.{max c h r})
  (M : SheafOfModulesOfCommRing R) (U : C)

-- Keep the actual evaluated module carrier at the original section comparison.
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the whole internal-Hom functor is the original additive Hom on the slice. -/
def sectionHomNatIso :
    homFunctor.{c, h, r} R M ⋙ SheafOfModules.evaluation
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (op U) ⋙
          forget₂ (ModuleCat _) AddCommGrpCat ≅
      SheafOfModules.overFunctor.{max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
          preadditiveCoyoneda.obj (op (M.over U)) :=
  NatIso.ofComponents (fun N => (sectionHomAddEquiv R M N U).toAddCommGrpIso) (fun b => by
    ext s
    change sectionHomAddEquiv R M _ U ((map R (𝟙 M) b).val.app (op U) s) =
      sectionHomAddEquiv R M _ U s ≫ (SheafOfModules.overFunctor _ U).map b
    rw [sectionHomAddEquiv_map, CategoryTheory.Functor.map_id, Category.id_comp])

/-- The whole section comparison uses the existing original section map. -/
theorem sectionHomNatIso_hom_app_apply (N : SheafOfModulesOfCommRing R)
    (s : (sheaf R M N).val.obj (op U)) :
    (sectionHomNatIso.{c, h, r} R M U).hom.app N s = sectionHomEquiv R M N U s := rfl

end SheafOfModules.InternalHom
