/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Ringed.ConstantRing
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Ringed.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Actual constant coefficients and native ringed module sheaves

The native module-sheafification adjunction restricts to an equivalence on
presheaves whose original abelian presheaf is already a sheaf. The unit is the
actual native unit and its underlying map is the original `toSheafify`; the
counit is the native module-sheafification counit. Constant scalar coefficients
enter this equivalence through their literal pointwise presheaf comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod.Ringed

universe u v r w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The actual module presheaves whose original underlying abelian presheaf is a sheaf. -/
def moduleSheafProperty (R₀ : Cᵒᵖ ⥤ RingCat.{r}) :
    ObjectProperty (PresheafOfModules.{w} R₀) := fun M => Presheaf.IsSheaf J M.presheaf

instance (R₀ : Cᵒᵖ ⥤ RingCat.{r}) :
    (moduleSheafProperty.{u, v, r, w} J R₀).IsClosedUnderIsomorphisms where
  of_iso e h := (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf R₀).mapIso e)).mp h

/-- The original abelian sheaf of a module presheaf already satisfying descent. -/
def moduleUnderlyingSheaf (R₀ : Cᵒᵖ ⥤ RingCat.{r}) :
    (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory ⥤ Sheaf J AddCommGrpCat.{w} where
  obj M := ⟨M.obj.presheaf, M.property⟩
  map f := ⟨(PresheafOfModules.toPresheaf R₀).map f.hom⟩

section Constant

variable (R : Type r) [Ring R]
variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

/-- Literal constant-ring conversion restricts to the actual sheaf categories. -/
def constantSheafEquivalence : Sheaf J (ModuleCat.{w} R) ≌
    (moduleSheafProperty.{u, v, r, w} J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).FullSubcategory :=
  (constantPresheafEquivalence (C := C) R).congrFullSubcategory (by
    funext P
    apply propext
    change Presheaf.IsSheaf J ((toConstantModules R).obj P).presheaf ↔ Presheaf.IsSheaf J P
    have h : Presheaf.IsSheaf J ((toConstantModules R).obj P).presheaf ↔
        Presheaf.IsSheaf J (P ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
      Presheaf.isSheaf_of_iso_iff ((toConstantModulesUnderlyingIso R).app P)
    exact h.trans ⟨Presheaf.isSheaf_of_isSheaf_comp J P _,
      fun h => GrothendieckTopology.HasSheafCompose.isSheaf P h⟩)

/-- The typed constant-ring comparison with the original abelian coefficient sheaf. -/
def constantSheafUnderlyingComponent (F : Sheaf J (ModuleCat.{w} R)) :
    (moduleUnderlyingSheaf.{u, v, r, w} J
      ((Functor.const Cᵒᵖ).obj (RingCat.of R))).obj
        ((constantSheafEquivalence J R).functor.obj F) ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F := by
  refine ObjectProperty.isoMk _ ?_
  change ((toConstantModules R).obj F.obj).presheaf ≅
    F.obj ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  exact (toConstantModulesUnderlyingIso R).app F.obj

/-- The constant-ring sheaf comparison keeps exactly the original abelian sheaf. -/
def constantSheafUnderlyingIso : (constantSheafEquivalence J R).functor ⋙
      moduleUnderlyingSheaf.{u, v, r, w} J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ≅
    sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
  NatIso.ofComponents (constantSheafUnderlyingComponent J R)
    (by intro F G f; apply ObjectProperty.hom_ext; ext X x; rfl)

end Constant

/-- The typed original adjunction unit on the actual full subcategory. -/
def adjunctionUnitIso
    {D E : Type*} [Category D] [Category E] (P : ObjectProperty D)
    {L : D ⥤ E} {G : E ⥤ D} (adj : L ⊣ G)
    (hG : ∀ Y, P (G.obj Y)) (hunit : ∀ X : P.FullSubcategory, IsIso (adj.unit.app X.obj)) :
    𝟭 P.FullSubcategory ≅ (P.ι ⋙ L) ⋙ P.lift G hG :=
  NatIso.ofComponents (fun X => by
    letI := hunit X
    exact ObjectProperty.isoMk P (X := X) (Y := (P.lift G hG).obj (L.obj X.obj))
      (asIso (adj.unit.app X.obj)))
        (by intro X Y f; apply ObjectProperty.hom_ext; exact adj.unit.naturality f.hom)

/-- The typed unit comparison has exactly the original underlying unit arrow. -/
@[simp]
theorem adjunctionUnitIso_hom_app_hom
    {D E : Type*} [Category D] [Category E] (P : ObjectProperty D)
    {L : D ⥤ E} {G : E ⥤ D} (adj : L ⊣ G)
    (hG : ∀ Y, P (G.obj Y)) (hunit : ∀ X : P.FullSubcategory, IsIso (adj.unit.app X.obj))
    (X : P.FullSubcategory) :
    ((adjunctionUnitIso P adj hG hunit).hom.app X).hom = adj.unit.app X.obj := rfl

/-- Restrict an actual adjunction with invertible counit to its actual unit-isomorphism
objects. The adjunction remains a typed parameter during the triangle proof. -/
def equivalenceOfSheafAdjunction
    {D E : Type*} [Category D] [Category E] (P : ObjectProperty D)
    {L : D ⥤ E} {G : E ⥤ D} (adj : L ⊣ G) [IsIso adj.counit]
    (hG : ∀ Y, P (G.obj Y)) (hunit : ∀ X : P.FullSubcategory, IsIso (adj.unit.app X.obj)) :
    P.FullSubcategory ≌ E where
  functor := P.ι ⋙ L
  inverse := P.lift G hG
  unitIso := adjunctionUnitIso P adj hG hunit
  counitIso := asIso adj.counit
  functor_unitIso_comp X := by
    change L.map (((adjunctionUnitIso P adj hG hunit).hom.app X).hom) ≫
      adj.counit.app (L.obj X.obj) = 𝟙 (L.obj X.obj)
    rw [adjunctionUnitIso_hom_app_hom]
    exact adj.left_triangle_components X.obj

section Native

variable {R₀ : Cᵒᵖ ⥤ RingCat.{r}} {R : Sheaf J RingCat.{r}} (α : R₀ ⟶ R.obj)
variable [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The original native unit is invertible whenever its original underlying presheaf is a sheaf. -/
theorem moduleUnit_isIso (M : (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory) :
    IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app M.obj) := by
  have : IsIso ((PresheafOfModules.toPresheaf R₀).map
      ((PresheafOfModules.sheafificationAdjunction α).unit.app M.obj)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.isIso_toSheafify J M.property
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf R₀)

/-- Restriction along the original ring-unit map, with the original abelian sheaf condition. -/
def fromRingedModules : SheafOfModules.{w} R ⥤
    (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory :=
  (moduleSheafProperty.{u, v, r, w} J R₀).lift
    (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α)
      (fun M => M.isSheaf)

/-- Native module sheafification is an equivalence on the actual already-sheaf coefficients. -/
def moduleSheafificationEquivalence :
    (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory ≌ SheafOfModules.{w} R :=
  equivalenceOfSheafAdjunction (moduleSheafProperty.{u, v, r, w} J R₀)
    (PresheafOfModules.sheafificationAdjunction α) (fun M => M.isSheaf)
      (moduleUnit_isIso J α)

/-- The underlying abelian comparison is the original native abelian-sheafification counit. -/
def moduleSheafificationUnderlyingIso : (moduleSheafificationEquivalence J (α := α)).functor ⋙
      SheafOfModules.toSheaf R ≅ moduleUnderlyingSheaf.{u, v, r, w} J R₀ :=
  NatIso.ofComponents (fun M =>
    asIso ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{w}).counit.app
      ((moduleUnderlyingSheaf.{u, v, r, w} J R₀).obj M)))
        (fun f => (CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{w}).counit.naturality
          ((moduleUnderlyingSheaf.{u, v, r, w} J R₀).map f))

/-- The original native module unit followed by the actual abelian comparison is the identity. -/
@[reassoc]
theorem moduleUnit_underlying_comparison
    (M : (moduleSheafProperty.{u, v, r, w} J R₀).FullSubcategory) :
    (PresheafOfModules.toPresheaf R₀).map
        ((PresheafOfModules.sheafificationAdjunction α).unit.app M.obj) ≫
      ((moduleSheafificationUnderlyingIso J (α := α)).hom.app M).hom = 𝟙 M.obj.presheaf := by
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact (CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{w}).right_triangle_components
    ((moduleUnderlyingSheaf.{u, v, r, w} J R₀).obj M)

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
