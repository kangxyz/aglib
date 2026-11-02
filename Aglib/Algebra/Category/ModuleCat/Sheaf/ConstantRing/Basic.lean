/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Equivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Arbitrary constant rings and their actual module sheaves

The associated ring sheaf, its original sheafification unit, and the
module-valued/ringed equivalence are constructed on an arbitrary site.
Site, ring and module-carrier universes remain separate; existence and
local-bijection hypotheses are required only where they are used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

universe u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ] [HasWeakSheafify J RingCat.{r}]

/-- The actual associated constant ring sheaf. -/
def constantRing : Sheaf J RingCat.{r} :=
  (constantSheaf J RingCat.{r}).obj (RingCat.of Λ)

/-- The original unit from the literal constant ring presheaf. -/
abbrev constantRingUnit :
    (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ (constantRing J Λ).obj :=
  CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))

/-- The ring construction retains the original constant-sheaf value. -/
theorem constantRing_eq_original :
    constantRing J Λ = (constantSheaf J RingCat.{r}).obj (RingCat.of Λ) := rfl

/-- The ring unit is the original native sheafification unit. -/
theorem constantRingUnit_eq_original :
    constantRingUnit J Λ =
      CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) := rfl

section LocallyBijective

variable [J.WEqualsLocallyBijective RingCat.{r}]

/-- The original constant-ring unit is locally injective. -/
instance constantRingUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective J (constantRingUnit J Λ) :=
  (J.W_toSheafify ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).isLocallyInjective

/-- The original constant-ring unit is locally surjective. -/
instance constantRingUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective J (constantRingUnit J Λ) :=
  (J.W_toSheafify ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).isLocallySurjective

end LocallyBijective

/-- Genuine module sheaves over the associated constant ring. -/
abbrev ModuleSheaf := SheafOfModules.{w} (constantRing J Λ)

/-- Sheaves valued in modules over the original coefficient ring. -/
abbrev ModuleValuedSheaf := Sheaf J (ModuleCat.{w} Λ)

section Equivalence

variable [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Native module sheafification over the actual constant-ring unit. -/
def constantModuleSheafificationEquivalence :
    (moduleSheafProperty.{u, v, r, w} J
      ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).FullSubcategory ≌
      ModuleSheaf.{u, v, r, w} J Λ :=
  moduleSheafificationEquivalence J (constantRingUnit J Λ)

/-- The actual equivalence is constant-presheaf conversion followed by native sheafification. -/
def moduleSheafEquivalence :
    ModuleValuedSheaf.{u, v, r, w} J Λ ≌ ModuleSheaf.{u, v, r, w} J Λ :=
  (constantSheafEquivalence J Λ).trans (constantModuleSheafificationEquivalence J Λ)

/-- The equivalence retains its two original construction factors. -/
theorem moduleSheafEquivalence_eq_original :
    moduleSheafEquivalence J Λ =
      (constantSheafEquivalence J Λ).trans
        (moduleSheafificationEquivalence J (constantRingUnit J Λ)) := rfl

/-- The underlying comparison is the original abelian sheafification counit. -/
def constantModuleSheafificationUnderlyingIso :
    (constantModuleSheafificationEquivalence J Λ).functor ⋙
      SheafOfModules.toSheaf (constantRing J Λ) ≅
    moduleUnderlyingSheaf.{u, v, r, w} J
      ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) :=
  moduleSheafificationUnderlyingIso J (constantRingUnit J Λ)

/-- The original coefficient equivalence preserves the actual underlying abelian sheaf. -/
def moduleSheafUnderlyingIso :
    (moduleSheafEquivalence J Λ).functor ⋙ SheafOfModules.toSheaf (constantRing J Λ) ≅
      sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (constantSheafEquivalence J Λ).functor
      (constantModuleSheafificationUnderlyingIso J Λ) ≪≫
    constantSheafUnderlyingIso J Λ

omit [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})] in
/-- The original native module unit followed by the actual underlying comparison is identity. -/
@[reassoc]
theorem constantModuleUnit_underlying_comparison
    (M : (moduleSheafProperty.{u, v, r, w} J
      ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).FullSubcategory) :
    (PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (constantRingUnit J Λ)).unit.app M.obj) ≫
      ((constantModuleSheafificationUnderlyingIso J Λ).hom.app M).hom =
        𝟙 M.obj.presheaf :=
  moduleUnit_underlying_comparison J (constantRingUnit J Λ) M

/-- The underlying comparison is natural for every original coefficient morphism. -/
@[reassoc]
theorem moduleSheafUnderlyingIso_naturality
    {M N : ModuleValuedSheaf.{u, v, r, w} J Λ} (f : M ⟶ N) :
    (SheafOfModules.toSheaf (constantRing J Λ)).map
        ((moduleSheafEquivalence J Λ).functor.map f) ≫
      (moduleSheafUnderlyingIso J Λ).hom.app N =
    (moduleSheafUnderlyingIso J Λ).hom.app M ≫
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map f :=
  (moduleSheafUnderlyingIso J Λ).hom.naturality f

end Equivalence

end ModuleCat.Sheaf.ConstantRing
