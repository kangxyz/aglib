/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.ExtensionByZero
public import Aglib.Topology.Sheaves.FreeAbelianPullback

/-!
# Extension by zero of the native free abelian sheaf on an open

The original extension-by-zero adjunction identifies the free abelian sheaf
on an open of a subspace with the native free abelian sheaf on its image in
the ambient space. The comparison retains the original represented-section
equivalences and is natural in the coefficient and the open.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u

variable {X : TopCat.{u}} (U : Opens X)

/-- The actual extension-by-zero adjunction identifies the two represented Hom functors. -/
def openFreeAbelianExtensionByZeroHomEquiv (V : Opens U)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((extensionByZero U).obj ((openFreeAbelianFunctor (TopCat.of U)).obj V) ⟶ F) ≃
      ((openFreeAbelianFunctor X).obj (U.isOpenEmbedding.functor.obj V) ⟶ F) :=
  (((extensionByZeroRestrictAdjunction U).homEquiv _ _).trans
    (openFreeAbelianHomEquiv (TopCat.of U) V
      ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F))).trans
        (openFreeAbelianHomEquiv X (U.isOpenEmbedding.functor.obj V) F).symm

/-- The original Hom comparison has its literal represented-section formula. -/
theorem openFreeAbelianExtensionByZeroHomEquiv_sections (V : Opens U)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (extensionByZero U).obj ((openFreeAbelianFunctor (TopCat.of U)).obj V) ⟶ F) :
    openFreeAbelianHomEquiv X (U.isOpenEmbedding.functor.obj V) F
        (openFreeAbelianExtensionByZeroHomEquiv U V F a) =
      openFreeAbelianHomEquiv (TopCat.of U) V
        ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F)
        (((extensionByZeroRestrictAdjunction U).homEquiv _ _) a) :=
  Equiv.apply_symm_apply _ _

/-- The represented extension-by-zero comparison is natural in the actual coefficient. -/
theorem openFreeAbelianExtensionByZeroHomEquiv_comp (V : Opens U)
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : (extensionByZero U).obj ((openFreeAbelianFunctor (TopCat.of U)).obj V) ⟶ F)
    (b : F ⟶ G) :
    openFreeAbelianExtensionByZeroHomEquiv U V G (a ≫ b) =
      openFreeAbelianExtensionByZeroHomEquiv U V F a ≫ b := by
  apply (openFreeAbelianHomEquiv X (U.isOpenEmbedding.functor.obj V) G).injective
  rw [openFreeAbelianExtensionByZeroHomEquiv_sections,
    openFreeAbelianHomEquiv_comp, openFreeAbelianExtensionByZeroHomEquiv_sections,
    Adjunction.homEquiv_naturality_right, openFreeAbelianHomEquiv_comp]
  rfl

/-- Native extension by zero sends the free abelian sheaf on an open to that on its image. -/
def openFreeAbelianExtensionByZeroObjIso (V : Opens U) :
    (extensionByZero U).obj ((openFreeAbelianFunctor (TopCat.of U)).obj V) ≅
      (openFreeAbelianFunctor X).obj (U.isOpenEmbedding.functor.obj V) where
  hom := (openFreeAbelianExtensionByZeroHomEquiv U V _).symm (𝟙 _)
  inv := openFreeAbelianExtensionByZeroHomEquiv U V _ (𝟙 _)
  hom_inv_id := by
    apply (openFreeAbelianExtensionByZeroHomEquiv U V _).injective
    rw [openFreeAbelianExtensionByZeroHomEquiv_comp, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := openFreeAbelianExtensionByZeroHomEquiv_comp U V (𝟙 _)
      ((openFreeAbelianExtensionByZeroHomEquiv U V _).symm (𝟙 _))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm

/-- The original comparison homomorphism has the native representing identity formula. -/
theorem openFreeAbelianExtensionByZeroHomEquiv_hom (V : Opens U) :
    openFreeAbelianExtensionByZeroHomEquiv U V _
        (openFreeAbelianExtensionByZeroObjIso U V).hom = 𝟙 _ :=
  Equiv.apply_symm_apply _ _

/-- The actual Hom comparison is precomposition with the original comparison inverse. -/
theorem openFreeAbelianExtensionByZeroHomEquiv_eq (V : Opens U)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (extensionByZero U).obj ((openFreeAbelianFunctor (TopCat.of U)).obj V) ⟶ F) :
    openFreeAbelianExtensionByZeroHomEquiv U V F a =
      (openFreeAbelianExtensionByZeroObjIso U V).inv ≫ a := by
  simpa only [Category.id_comp, openFreeAbelianExtensionByZeroObjIso] using
    openFreeAbelianExtensionByZeroHomEquiv_comp U V (𝟙 _) a

/-- The original Hom comparison is natural in the open of the subspace. -/
theorem openFreeAbelianExtensionByZeroHomEquiv_naturality {V W : Opens U} (i : V ⟶ W)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (extensionByZero U).obj ((openFreeAbelianFunctor (TopCat.of U)).obj W) ⟶ F) :
    openFreeAbelianExtensionByZeroHomEquiv U V F
        ((extensionByZero U).map ((openFreeAbelianFunctor (TopCat.of U)).map i) ≫ a) =
      (openFreeAbelianFunctor X).map (U.isOpenEmbedding.functor.map i) ≫
        openFreeAbelianExtensionByZeroHomEquiv U W F a := by
  apply (openFreeAbelianHomEquiv X (U.isOpenEmbedding.functor.obj V) F).injective
  rw [openFreeAbelianExtensionByZeroHomEquiv_sections, Adjunction.homEquiv_naturality_left,
    openFreeAbelianHomEquiv_naturality, openFreeAbelianHomEquiv_naturality,
    openFreeAbelianExtensionByZeroHomEquiv_sections]
  rfl

/-- The native free-open comparison is functorial in the original open. -/
def openFreeAbelianExtensionByZeroIso :
    openFreeAbelianFunctor (TopCat.of U) ⋙ extensionByZero U ≅
      U.isOpenEmbedding.functor ⋙ openFreeAbelianFunctor X :=
  NatIso.ofComponents (openFreeAbelianExtensionByZeroObjIso U) (by
    intro V W i
    apply (openFreeAbelianExtensionByZeroHomEquiv U V _).injective
    dsimp only [Functor.comp_map, Functor.comp_obj]
    erw [openFreeAbelianExtensionByZeroHomEquiv_naturality U i _
      (openFreeAbelianExtensionByZeroObjIso U W).hom]
    erw [openFreeAbelianExtensionByZeroHomEquiv_comp U V
      (openFreeAbelianExtensionByZeroObjIso U V).hom
      ((openFreeAbelianFunctor X).map (U.isOpenEmbedding.functor.map i))]
    rw [openFreeAbelianExtensionByZeroHomEquiv_hom,
      openFreeAbelianExtensionByZeroHomEquiv_hom, Category.comp_id, Category.id_comp])

end TopCat.Sheaf
