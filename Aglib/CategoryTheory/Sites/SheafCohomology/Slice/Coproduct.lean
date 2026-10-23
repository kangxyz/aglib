/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# The coproduct left adjoint to slice restriction

The value at `V` is the coproduct over the actual arrows `V ⟶ U`.
Only hom-sized coproducts are used; there is no smallness assumption on the
objects of the site and no full-faithfulness assumption on `Over.forget U`.
-/

@[expose] public noncomputable section

universe v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A]

/-- The family of summands over an object of the original category. -/
abbrev summands (U : C) (G : (Over U)ᵒᵖ ⥤ A) (V : C) : (V ⟶ U) → A :=
  fun f ↦ G.obj (op (Over.mk f))

/-- The restriction map of the coproduct extension. -/
def coproductRestriction (U : C) (G : (Over U)ᵒᵖ ⥤ A)
    {V W : C} (h : W ⟶ V) : ∐ (summands U G V) ⟶ ∐ (summands U G W) :=
  Limits.Sigma.desc fun f ↦ G.map (Over.homMk h : Over.mk (h ≫ f) ⟶ Over.mk f).op ≫
    Limits.Sigma.ι (summands U G W) (h ≫ f)

@[reassoc (attr := simp)]
theorem ι_coproductRestriction (U : C) (G : (Over U)ᵒᵖ ⥤ A)
    {V W : C} (h : W ⟶ V) (f : V ⟶ U) :
    Limits.Sigma.ι (summands U G V) f ≫ coproductRestriction U G h =
      G.map (Over.homMk h : Over.mk (h ≫ f) ⟶ Over.mk f).op ≫
        Limits.Sigma.ι (summands U G W) (h ≫ f) := by
  simp [coproductRestriction]

/-- A version with a prescribed target index avoids dependent rewriting of summands. -/
@[reassoc]
theorem ι_coproductRestriction_of_eq (U : C) (G : (Over U)ᵒᵖ ⥤ A)
    {V W : C} (h : W ⟶ V) (f : V ⟶ U) (g : W ⟶ U) (w : h ≫ f = g) :
    Limits.Sigma.ι (summands U G V) f ≫ coproductRestriction U G h =
      G.map (Over.homMk h w : Over.mk g ⟶ Over.mk f).op ≫
        Limits.Sigma.ι (summands U G W) g := by
  subst g
  exact ι_coproductRestriction U G h f

/-- The explicit extension of a presheaf from the slice. -/
def coproductExtensionObj (U : C) (G : (Over U)ᵒᵖ ⥤ A) : Cᵒᵖ ⥤ A where
  obj V := ∐ (summands U G V.unop)
  map h := coproductRestriction U G h.unop
  map_id V := by
    apply Limits.Sigma.hom_ext
    intro f
    change Limits.Sigma.ι _ f ≫ coproductRestriction U G (𝟙 V.unop) = _
    rw [ι_coproductRestriction_of_eq U G _ f f (Category.id_comp f)]
    have e : (Over.homMk (𝟙 V.unop) (Category.id_comp f) : Over.mk f ⟶ Over.mk f) =
        𝟙 _ := by ext; rfl
    rw [e]
    simp
  map_comp {V W Z} h k := by
    apply Limits.Sigma.hom_ext
    intro f
    change Limits.Sigma.ι _ f ≫ coproductRestriction U G (k.unop ≫ h.unop) =
      Limits.Sigma.ι _ f ≫ (coproductRestriction U G h.unop ≫ coproductRestriction U G k.unop)
    rw [ι_coproductRestriction_of_eq U G _ f (k.unop ≫ (h.unop ≫ f))
      (Category.assoc _ _ _)]
    simp only [ι_coproductRestriction_assoc, ι_coproductRestriction]
    rw [← G.map_comp_assoc]
    congr 2

/-- Extension acts on each summand by the original coefficient morphism. -/
def coproductExtensionMap (U : C) {G H : (Over U)ᵒᵖ ⥤ A} (α : G ⟶ H) :
    coproductExtensionObj U G ⟶ coproductExtensionObj U H where
  app V := Limits.Sigma.map fun f ↦ α.app (op (Over.mk f))
  naturality {V W} h := by
    apply Limits.Sigma.hom_ext
    intro f
    simp only [coproductExtensionObj, ι_coproductRestriction_assoc, Limits.Sigma.ι_map_assoc,
      ι_coproductRestriction, Limits.Sigma.ι_map]
    rw [← α.naturality_assoc]

/-- The hom-sized coproduct extension functor. -/
def coproductExtension (U : C) : ((Over U)ᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A where
  obj := coproductExtensionObj U
  map := coproductExtensionMap U
  map_id G := by
    ext V
    exact Limits.Sigma.map_id
  map_comp α β := by
    ext V
    exact (Limits.Sigma.map_comp_map (fun f ↦ β.app (op (Over.mk f)))
      (fun f ↦ α.app (op (Over.mk f)))).symm

/-- Slice restriction before sheafification. -/
abbrev presheafRestriction (U : C) : (Cᵒᵖ ⥤ A) ⥤ (Over U)ᵒᵖ ⥤ A :=
  (Functor.whiskeringLeft _ _ A).obj (Over.forget U).op

/-- Extract a slice morphism using the designated summand. -/
def restrictHom (U : C) {G : (Over U)ᵒᵖ ⥤ A} {F : Cᵒᵖ ⥤ A}
    (α : coproductExtensionObj U G ⟶ F) : G ⟶ (presheafRestriction U).obj F where
  app V := Limits.Sigma.ι (summands U G V.unop.left) V.unop.hom ≫ α.app (op V.unop.left)
  naturality {V W} h := by
    have e := congrArg (fun k ↦ Limits.Sigma.ι (summands U G V.unop.left) V.unop.hom ≫ k)
      (α.naturality ((Over.forget U).map h.unop).op)
    change Limits.Sigma.ι (summands U G V.unop.left) V.unop.hom ≫
      (coproductRestriction U G h.unop.left ≫ α.app (op W.unop.left)) = _ at e
    have e' := (ι_coproductRestriction_of_eq_assoc U G h.unop.left V.unop.hom W.unop.hom
      (Over.w h.unop) (α.app (op W.unop.left))).symm.trans e
    have he : (Over.homMk h.unop.left (Over.w h.unop) : W.unop ⟶ V.unop) = h.unop := by
      ext
      rfl
    simpa only [he, Quiver.Hom.op_unop] using! e'.trans
      (Category.assoc (Limits.Sigma.ι (summands U G V.unop.left) V.unop.hom)
        (α.app (op V.unop.left)) (F.map h.unop.left.op)).symm

/-- Assemble a morphism from the coproduct by its summands. -/
def extendHom (U : C) {G : (Over U)ᵒᵖ ⥤ A} {F : Cᵒᵖ ⥤ A}
    (β : G ⟶ (presheafRestriction U).obj F) : coproductExtensionObj U G ⟶ F where
  app V := Limits.Sigma.desc fun f ↦ β.app (op (Over.mk f))
  naturality {V W} h := by
    apply Limits.Sigma.hom_ext
    intro f
    simp only [coproductExtensionObj, ι_coproductRestriction_assoc,
      Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc_assoc]
    exact β.naturality (Over.homMk h.unop :
      Over.mk (h.unop ≫ f) ⟶ Over.mk f).op

/-- The coproduct adjunction is the literal summandwise hom equivalence. -/
def coproductHomEquiv (U : C) (G : (Over U)ᵒᵖ ⥤ A) (F : Cᵒᵖ ⥤ A) :
    (coproductExtensionObj U G ⟶ F) ≃ (G ⟶ (presheafRestriction U).obj F) where
  toFun := restrictHom U
  invFun := extendHom U
  left_inv α := by
    ext V
    apply Limits.Sigma.hom_ext
    intro f
    simp [extendHom, restrictHom]
  right_inv β := by
    ext V
    simp [restrictHom, extendHom]
    rfl

/-- The actual left adjunction to precomposition by `Over.forget U`. -/
def coproductAdjunction (U : C) : coproductExtension (A := A) U ⊣ presheafRestriction U :=
  Adjunction.mkOfHomEquiv {
    homEquiv := coproductHomEquiv U
    homEquiv_naturality_left_symm := by
      intro G H F α β
      change extendHom U (α ≫ β) = coproductExtensionMap U α ≫ extendHom U β
      ext V
      apply Limits.Sigma.hom_ext
      intro f
      simp [extendHom, coproductExtensionMap]
      simpa only [Limits.Sigma.ι_comp_desc] using!
        (Limits.Sigma.ι_map_assoc (fun f : V.unop ⟶ U ↦ α.app (op (Over.mk f))) f
          (Limits.Sigma.desc fun f : V.unop ⟶ U ↦
            (show H.obj (op (Over.mk f)) ⟶ F.obj V from β.app (op (Over.mk f))))).symm
    homEquiv_naturality_right := by
      intro G F H α β
      change restrictHom U (α ≫ β) = restrictHom U α ≫ (presheafRestriction U).map β
      ext V
      exact (Category.assoc (Limits.Sigma.ι (summands U G V.unop.left) V.unop.hom)
        (α.app (op V.unop.left)) (β.app (op V.unop.left))).symm }

end CategoryTheory.Sheaf.SliceCohomology
