/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Canonical ZMod-valued sheaves with the original abelian coefficients

Literal annihilation of an abelian sheaf produces a genuine module-valued
sheaf on the same site, with the same original sections and restriction maps.
Native limit reflection proves the sheaf condition without a size restriction.
The underlying native `sheafCompose` comparison requires only its actual
sheaf-composition instance, supplied by native limit preservation when the
value universe contains the site object and morphism universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

/-- The literal identity-annihilation equation annihilates each original sheaf section. -/
theorem sheafSectionsKilled (F : Sheaf J AddCommGrpCat.{w})
    (hF : n • 𝟙 F = 0) (X : Cᵒᵖ) (x : F.obj.obj X) : n • x = 0 := by
  have h := congrArg (fun f : F ⟶ F => f.hom.app X x) hF
  exact h

/-- The original abelian sheaf as a genuine ZMod-valued sheaf, including modulus zero. -/
def sheaf (F : Sheaf J AddCommGrpCat.{w}) (hF : n • 𝟙 F = 0) :
    Sheaf J (ModuleCat.{w} (ZMod n)) where
  obj := presheaf n F.obj (sheafSectionsKilled J n F hF)
  property := Presheaf.isSheaf_of_isSheaf_comp J _
    (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})
      ((Presheaf.isSheaf_of_iso_iff
        (presheafUnderlyingIso n F.obj (sheafSectionsKilled J n F hF))).mpr F.property)

@[simp]
theorem sheaf_map_apply (F : Sheaf J AddCommGrpCat.{w}) (hF : n • 𝟙 F = 0)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj.obj X) :
    (sheaf J n F hF).obj.map f x = F.obj.map f x := rfl

/-- Every original coefficient arrow canonically lifts to an arrow of the genuine module sheaves. -/
def sheafMap {F G : Sheaf J AddCommGrpCat.{w}}
    (hF : n • 𝟙 F = 0) (hG : n • 𝟙 G = 0) (f : F ⟶ G) :
    sheaf J n F hF ⟶ sheaf J n G hG :=
  ⟨presheafMap n (sheafSectionsKilled J n F hF) (sheafSectionsKilled J n G hG) f.hom⟩

@[simp]
theorem sheafMap_hom_app_apply {F G : Sheaf J AddCommGrpCat.{w}}
    (hF : n • 𝟙 F = 0) (hG : n • 𝟙 G = 0) (f : F ⟶ G)
    (X : Cᵒᵖ) (x : F.obj.obj X) : (sheafMap J n hF hG f).hom.app X x = f.hom.app X x := rfl

@[simp]
theorem sheafMap_id (F : Sheaf J AddCommGrpCat.{w}) (hF : n • 𝟙 F = 0) :
    sheafMap J n hF hF (𝟙 F) = 𝟙 (sheaf J n F hF) := by
  apply ObjectProperty.hom_ext
  exact presheafMap_id n _

@[simp]
theorem sheafMap_comp {F G H : Sheaf J AddCommGrpCat.{w}}
    (hF : n • 𝟙 F = 0) (hG : n • 𝟙 G = 0) (hH : n • 𝟙 H = 0)
    (f : F ⟶ G) (g : G ⟶ H) :
    sheafMap J n hF hH (f ≫ g) = sheafMap J n hF hG f ≫ sheafMap J n hG hH g := by
  apply ObjectProperty.hom_ext
  exact presheafMap_comp n _ _ _ f.hom g.hom

/-- The actual full subcategory of sheaves killed by the literal scalar identity equation. -/
def killedSheaves : ObjectProperty (Sheaf J AddCommGrpCat.{w}) := fun F => n • 𝟙 F = 0

/-- Canonical scalar conversion, functorial for every original coefficient morphism. -/
def sheafFunctor : (killedSheaves.{u, v, w} J n).FullSubcategory ⥤
    Sheaf J (ModuleCat.{w} (ZMod n)) where
  obj F := sheaf J n F.obj F.property
  map {F G} f := sheafMap J n F.property G.property f.hom
  map_id F := sheafMap_id J n F.obj F.property
  map_comp {F G H} f g := sheafMap_comp J n F.property G.property H.property f.hom g.hom

section Underlying

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]

/-- The native underlying abelian sheaf is canonically the original coefficient sheaf. -/
def sheafUnderlyingIso (F : Sheaf J AddCommGrpCat.{w}) (hF : n • 𝟙 F = 0) :
    (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj
        (sheaf J n F hF) ≅ F :=
  ObjectProperty.isoMk _ (presheafUnderlyingIso n F.obj (sheafSectionsKilled J n F hF))

@[simp]
theorem sheafUnderlyingIso_hom_app (F : Sheaf J AddCommGrpCat.{w})
    (hF : n • 𝟙 F = 0) (X : Cᵒᵖ) :
    (sheafUnderlyingIso J n F hF).hom.hom.app X = 𝟙 (F.obj.obj X) := rfl

/-- The underlying sheaf comparison is natural in every original coefficient map. -/
@[reassoc]
theorem sheafMap_underlying {F G : Sheaf J AddCommGrpCat.{w}}
    (hF : n • 𝟙 F = 0) (hG : n • 𝟙 G = 0) (f : F ⟶ G) :
    (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).map
        (sheafMap J n hF hG f) ≫ (sheafUnderlyingIso J n G hG).hom =
      (sheafUnderlyingIso J n F hF).hom ≫ f := by
  apply ObjectProperty.hom_ext
  exact presheafMap_underlying n _ _ f.hom

/-- The exact underlying-sheaf natural isomorphism for canonical scalar conversion. -/
def sheafFunctorUnderlyingIso :
    sheafFunctor.{u, v, w} J n ⋙
        sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}) ≅
      (killedSheaves.{u, v, w} J n).ι :=
  NatIso.ofComponents (fun F => sheafUnderlyingIso J n F.obj F.property)
    (fun f => sheafMap_underlying J n _ _ f.hom)

end Underlying

/-- Native sheaf composition is available whenever the value universe contains the
site object and morphism universes. The scalar ring itself is not resized. -/
theorem hasSheafCompose_of_univLE [UnivLE.{max u v, w}] :
    J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}) := inferInstance

/-- At the standard value universe, the original sheaf comparison has no extra
sheaf-composition premise. This also covers sites of size `u + 1` with values there. -/
def sheafFunctorUnderlyingIsoStandard :
    sheafFunctor.{u, v, max u v} J n ⋙
        sheafCompose J
          (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v}) ≅
      (killedSheaves.{u, v, max u v} J n).ι :=
  sheafFunctorUnderlyingIso J n

end CategoryTheory.TorsionZMod
