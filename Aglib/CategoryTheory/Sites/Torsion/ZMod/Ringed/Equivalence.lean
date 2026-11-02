/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Equivalence
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Ringed.ConstantRing
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Ringed.Presheaf

/-! # Compatibility for ringed coefficients and genuine ZMod scalar transport

Arbitrary-ring equivalences are implemented in the general coefficient owner.
The historical names and genuinely ZMod scalar constructions remain available.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod.Ringed

universe u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The actual module presheaves whose original underlying abelian presheaf is a sheaf. -/
abbrev moduleSheafProperty (R₀ : Cᵒᵖ ⥤ RingCat.{r}) :
    ObjectProperty (PresheafOfModules.{w} R₀) :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafProperty J R₀

/-- The original abelian sheaf of a module presheaf already satisfying descent. -/
abbrev moduleUnderlyingSheaf (R₀ : Cᵒᵖ ⥤ RingCat.{r}) :
    (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory ⥤ Sheaf J AddCommGrpCat.{w} :=
  ModuleCat.Sheaf.ConstantRing.moduleUnderlyingSheaf J R₀

section Constant

variable (R : Type r) [Ring R]
variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

/-- Literal constant-ring conversion restricts to the actual sheaf categories. -/
abbrev constantSheafEquivalence :
    Sheaf J (ModuleCat.{w} R) ≌
      (moduleSheafProperty.{u, v, r, w} J
        ((Functor.const Cᵒᵖ).obj (RingCat.of R))).FullSubcategory :=
  ModuleCat.Sheaf.ConstantRing.constantSheafEquivalence J R

/-- The typed constant-ring comparison with the original abelian coefficient sheaf. -/
abbrev constantSheafUnderlyingComponent (F : Sheaf J (ModuleCat.{w} R)) :
    (moduleUnderlyingSheaf.{u, v, r, w} J
      ((Functor.const Cᵒᵖ).obj (RingCat.of R))).obj
        ((constantSheafEquivalence J R).functor.obj F) ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F :=
  ModuleCat.Sheaf.ConstantRing.constantSheafUnderlyingComponent J R F

/-- The constant-ring sheaf comparison keeps exactly the original abelian sheaf. -/
abbrev constantSheafUnderlyingIso : (constantSheafEquivalence J R).functor ⋙
      moduleUnderlyingSheaf.{u, v, r, w} J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ≅
    sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
  ModuleCat.Sheaf.ConstantRing.constantSheafUnderlyingIso J R

end Constant

/-- The typed original adjunction unit on the actual full subcategory. -/
abbrev adjunctionUnitIso
    {D E : Type*} [Category D] [Category E] (P : ObjectProperty D)
    {L : D ⥤ E} {G : E ⥤ D} (adj : L ⊣ G)
    (hG : ∀ Y, P (G.obj Y)) (hunit : ∀ X : P.FullSubcategory, IsIso (adj.unit.app X.obj)) :
    𝟭 P.FullSubcategory ≅ (P.ι ⋙ L) ⋙ P.lift G hG :=
  ModuleCat.Sheaf.ConstantRing.adjunctionUnitIso P adj hG hunit

/-- The typed unit comparison has exactly the original underlying unit arrow. -/
theorem adjunctionUnitIso_hom_app_hom
    {D E : Type*} [Category D] [Category E] (P : ObjectProperty D)
    {L : D ⥤ E} {G : E ⥤ D} (adj : L ⊣ G)
    (hG : ∀ Y, P (G.obj Y)) (hunit : ∀ X : P.FullSubcategory, IsIso (adj.unit.app X.obj))
    (X : P.FullSubcategory) :
    ((adjunctionUnitIso P adj hG hunit).hom.app X).hom = adj.unit.app X.obj :=
  ModuleCat.Sheaf.ConstantRing.adjunctionUnitIso_hom_app_hom P adj hG hunit X

/-- Restrict an actual adjunction with invertible counit to its actual unit-isomorphism
objects. The adjunction remains a typed parameter during the triangle proof. -/
abbrev equivalenceOfSheafAdjunction
    {D E : Type*} [Category D] [Category E] (P : ObjectProperty D)
    {L : D ⥤ E} {G : E ⥤ D} (adj : L ⊣ G) [IsIso adj.counit]
    (hG : ∀ Y, P (G.obj Y)) (hunit : ∀ X : P.FullSubcategory, IsIso (adj.unit.app X.obj)) :
    P.FullSubcategory ≌ E :=
  ModuleCat.Sheaf.ConstantRing.equivalenceOfSheafAdjunction P adj hG hunit

section Native

variable {R₀ : Cᵒᵖ ⥤ RingCat.{r}} {R : Sheaf J RingCat.{r}} (α : R₀ ⟶ R.obj)
variable [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The original native unit is invertible whenever its original underlying presheaf is a sheaf. -/
theorem moduleUnit_isIso (M : (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory) :
    IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app M.obj) :=
  ModuleCat.Sheaf.ConstantRing.moduleUnit_isIso J α M

/-- Restriction along the original ring-unit map, with the original abelian sheaf condition. -/
abbrev fromRingedModules : SheafOfModules.{w} R ⥤
    (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory :=
  ModuleCat.Sheaf.ConstantRing.fromRingedModules J α

/-- Native module sheafification is an equivalence on the actual already-sheaf coefficients. -/
abbrev moduleSheafificationEquivalence :
    (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory ≌ SheafOfModules.{w} R :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafificationEquivalence J α

/-- The underlying abelian comparison is the original native abelian-sheafification counit. -/
abbrev moduleSheafificationUnderlyingIso :
    (moduleSheafificationEquivalence J (α := α)).functor ⋙
      SheafOfModules.toSheaf R ≅ moduleUnderlyingSheaf.{u, v, r, w} J R₀ :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafificationUnderlyingIso J (α := α)

/-- The original native module unit followed by the actual abelian comparison is the identity. -/
@[reassoc]
theorem moduleUnit_underlying_comparison
    (M : (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory) :
    (PresheafOfModules.toPresheaf R₀).map
        ((PresheafOfModules.sheafificationAdjunction α).unit.app M.obj) ≫
      ((moduleSheafificationUnderlyingIso J (α := α)).hom.app M).hom = 𝟙 M.obj.presheaf :=
  ModuleCat.Sheaf.ConstantRing.moduleUnit_underlying_comparison J α M

end Native

section Scalars

variable (n : ℕ)

/-- The actual scalar RingEquiv induces an equivalence of genuine sheaf categories. -/
def scalarSheafEquivalence : Sheaf J (ModuleCat.{w} (ZMod n)) ≌
    Sheaf J (ModuleCat.{w} (ULift.{w} (ZMod n))) := by
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (Presheaf.IsSheaf J : ObjectProperty
        (Cᵒᵖ ⥤ ModuleCat.{w} (ULift.{w} (ZMod n)))) := {
    of_iso e h := (Presheaf.isSheaf_of_iso_iff e).mp h }
  exact (scalarEquivalence.{w} n).congrRight.congrFullSubcategory (by
    funext P
    apply propext
    exact ⟨Presheaf.isSheaf_of_isSheaf_comp J P _,
      Presheaf.isSheaf_comp_of_isSheaf J P _⟩)

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w})]

/-- The typed original section comparison for actual scalar transport. -/
def scalarUnderlyingComponent (F : Sheaf J (ModuleCat.{w} (ZMod n))) (X : Cᵒᵖ) :
    ((sheafCompose J
        (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w})).obj
      ((scalarSheafEquivalence J n).functor.obj F)).obj.obj X ≅
    ((sheafCompose J
      (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj F).obj.obj X where
  hom := AddCommGrpCat.ofHom {
    toFun := fun x => x
    map_zero' := rfl
    map_add' := by intros; rfl }
  inv := AddCommGrpCat.ofHom {
    toFun := fun x => x
    map_zero' := rfl
    map_add' := by intros; rfl }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

/-- Actual scalar transport changes the scalar action and preserves every original additive map. -/
def scalarSheafUnderlyingIso : (scalarSheafEquivalence J n).functor ⋙
      sheafCompose J
        (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w}) ≅
    sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}) :=
  NatIso.ofComponents (fun F => ObjectProperty.isoMk _
    (NatIso.ofComponents (scalarUnderlyingComponent J n F) (by intros; ext x; rfl)))
      (by intros; apply ObjectProperty.hom_ext; ext X x; rfl)

end Scalars

end CategoryTheory.TorsionZMod.Ringed
