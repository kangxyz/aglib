/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free

/-!
# Free module presheaves with independent scalar size

The coefficient ring is not resized. Free modules use finitely supported
functions on the indicated basis, in the maximum of the two actual universes.
-/

@[expose] public noncomputable section

open CategoryTheory

universe r w u v

namespace ModuleCat

/-- Free modules with scalar and basis universes independent. -/
def freeWide (R : Type r) [Ring R] (X : Type w) : ModuleCat.{max r w} R :=
  ModuleCat.of R (X →₀ R)

/-- The universal map from a free module, without resizing its scalars. -/
def freeWideDesc {R : Type r} [Ring R] {X : Type w}
    {M : ModuleCat.{max r w} R} (f : X → M) : freeWide R X ⟶ M :=
  ModuleCat.ofHom (Finsupp.lift M R X f)

@[simp] theorem freeWideDesc_single {R : Type r} [Ring R] {X : Type w}
    {M : ModuleCat.{max r w} R} (f : X → M) (x : X) :
    freeWideDesc f (Finsupp.single x 1) = f x := by
  dsimp [freeWideDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[ext] theorem freeWide_hom_ext {R : Type r} [Ring R] {X : Type w}
    {M : ModuleCat.{max r w} R} {f g : freeWide R X ⟶ M}
    (h : ∀ x, f (Finsupp.single x 1) = g (Finsupp.single x 1)) : f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The free-module functor with independent scalar and generator universes. -/
def freeWideFunctor (R : Type r) [Ring R] : Type w ⥤ ModuleCat.{max r w} R where
  obj X := freeWide R X
  map f := freeWideDesc (fun x ↦ Finsupp.single (f x) 1)
  map_id X := by
    apply freeWide_hom_ext
    intro x
    exact freeWideDesc_single (R := R) (M := freeWide R X)
      (fun x ↦ Finsupp.single x (1 : R)) x
  map_comp {X Y Z} f g := by
    apply freeWide_hom_ext
    intro x
    change freeWideDesc (R := R) (M := freeWide R Z)
        (fun x ↦ Finsupp.single (g (f x)) 1) (Finsupp.single x 1) =
      freeWideDesc (R := R) (M := freeWide R Z) (fun y ↦ Finsupp.single (g y) 1)
        (freeWideDesc (R := R) (M := freeWide R Y)
          (fun x ↦ Finsupp.single (f x) 1) (Finsupp.single x 1))
    rw [freeWideDesc_single, freeWideDesc_single, freeWideDesc_single]

end ModuleCat

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{r}}

set_option backward.isDefEq.respectTransparency.types false in
/-- A free presheaf with genuinely independent coefficient and basis universes. -/
def freeWideObj (F : Cᵒᵖ ⥤ Type w) : PresheafOfModules.{max r w} R where
  obj X := ModuleCat.freeWide (R.obj X) (F.obj X)
  map {X Y} f := ModuleCat.freeWideDesc (fun x ↦ Finsupp.single (F.map f x) 1)
  map_id := by intros; ext x; simp
  map_comp := by intros; ext x; simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Universal description of a morphism out of a free presheaf. -/
def freeWideObjDesc {F : Cᵒᵖ ⥤ Type (max r w)}
    {M : PresheafOfModules.{max r w} R} (φ : F ⟶ M.presheaf ⋙ forget _) :
    freeWideObj (R := R) F ⟶ M where
  app X := ModuleCat.freeWideDesc (φ.app X)
  naturality {X Y} f := by
    apply ModuleCat.freeWide_hom_ext
    intro x
    simpa [freeWideObj, presheaf] using! (NatTrans.naturality_apply φ f x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The basis inclusion into the underlying presheaf. -/
def freeWideUnit (R : Cᵒᵖ ⥤ RingCat.{r}) (F : Cᵒᵖ ⥤ Type (max r w)) :
    F ⟶ (freeWideObj (R := R) F).presheaf ⋙ forget _ where
  app X := ↾fun x ↦ Finsupp.single x 1
  naturality := by intros; ext x; simp [freeWideObj, presheaf]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Free-module maps represent maps from the basis, over the original small ring. -/
def freeWideHomEquiv {F : Cᵒᵖ ⥤ Type (max r w)}
    {M : PresheafOfModules.{max r w} R} :
    (freeWideObj (R := R) F ⟶ M) ≃ (F ⟶ M.presheaf ⋙ forget _) where
  toFun ψ := freeWideUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _
  invFun := freeWideObjDesc
  left_inv ψ := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.freeWide_hom_ext
    intro x
    simp [freeWideUnit, freeWideObjDesc, toPresheaf]
    rfl
  right_inv φ := by
    ext X x
    change ModuleCat.freeWideDesc (φ.app X) (Finsupp.single x 1) = φ.app X x
    exact ModuleCat.freeWideDesc_single _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Free presheaves with independent scalar size, using the universal maps. -/
def freeWide (R : Cᵒᵖ ⥤ RingCat.{r}) :
    (Cᵒᵖ ⥤ Type (max r w)) ⥤ PresheafOfModules.{max r w} R where
  obj := freeWideObj
  map {F G} φ := freeWideObjDesc (φ ≫ freeWideUnit R G)
  map_id := by
    intro F
    apply freeWideHomEquiv.{r, w, u, v}.injective
    ext X x
    change ModuleCat.freeWideDesc (R := R.obj X)
      (M := ModuleCat.freeWide (R.obj X) (F.obj X)) (fun x ↦ Finsupp.single x 1)
      (Finsupp.single x 1) = Finsupp.single x 1
    exact ModuleCat.freeWideDesc_single _ _
  map_comp := by
    intros F G H f g
    apply freeWideHomEquiv.{r, w, u, v}.injective
    ext X x
    change ModuleCat.freeWideDesc (R := R.obj X)
        (M := ModuleCat.freeWide (R.obj X) (H.obj X))
        (fun x ↦ Finsupp.single (g.app X (f.app X x)) 1)
        (Finsupp.single x 1) =
      ModuleCat.freeWideDesc (R := R.obj X)
        (M := ModuleCat.freeWide (R.obj X) (H.obj X))
        (fun x ↦ Finsupp.single (g.app X x) 1)
        (ModuleCat.freeWideDesc (R := R.obj X)
          (M := ModuleCat.freeWide (R.obj X) (G.obj X))
          (fun x ↦ Finsupp.single (f.app X x) 1)
          (Finsupp.single x 1))
    simp only [ModuleCat.freeWideDesc_single]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Independent-scalar free presheaves are left adjoint to the actual forgetful functor. -/
def freeWideAdjunction (R : Cᵒᵖ ⥤ RingCat.{r}) :
    freeWide.{r, w, u, v} R ⊣
      (toPresheaf R ⋙ (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{max r w})) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ freeWideHomEquiv.{r, w, u, v}
      homEquiv_naturality_left_symm := fun {F G M} f g ↦ by
        apply freeWideHomEquiv.{r, w, u, v}.injective
        ext X x
        change ModuleCat.freeWideDesc (R := R.obj X) (M := M.obj X)
            (fun x ↦ g.app X (f.app X x)) (Finsupp.single x 1) =
          ModuleCat.freeWideDesc (R := R.obj X) (M := M.obj X) (g.app X)
            (ModuleCat.freeWideDesc (R := R.obj X)
              (M := ModuleCat.freeWide (R.obj X) (G.obj X))
              (fun x ↦ Finsupp.single (f.app X x) 1) (Finsupp.single x 1))
        simp only [ModuleCat.freeWideDesc_single]
      homEquiv_naturality_right := fun {F M N} f g ↦ rfl }

end PresheafOfModules
