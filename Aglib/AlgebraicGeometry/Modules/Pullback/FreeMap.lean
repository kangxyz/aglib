/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FreeComp

/-!
# Maps out of free sheaves under pullback

For a morphism of schemes `q : Y ⟶ X` and a map `m : free I ⟶ F` of `𝒪_X`-modules,
`pullbackFreeMap q m : free I ≅ q^* free I ⟶ q^* F` is its pullback, through the inverse of
`pullbackFreeIso q I`. It respects composition and equality of morphisms (`pullbackFreeMap_comp`,
`pullbackFreeMap_congr`) and composition of maps (`pullbackFreeMap_comp_right`); the inverse free
isomorphisms respect composition (`pullbackFreeIso_inv_comp`). On a basis inclusion
`ιFree i : 𝒪 ⟶ free I`, the free isomorphism is the unit isomorphism
(`pullback_map_ιFree_comp_pullbackFreeIso_hom`, from Mathlib's
`SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`, and its inverse form
`ιFree_comp_pullbackFreeIso_inv`).

No hypothesis on `q`, `F` or `I` is needed. The direct-image counterpart `pushforwardFreeMap` and
the base-change identities are in `Modules/BaseChange/FreeMap`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} {I : Type u}

/-- The pullback `free I ≅ q^* free I ⟶ q^* F` of a map `m : free I ⟶ F` out of a free sheaf. -/
def pullbackFreeMap (q : Y ⟶ X) {F : X.Modules} (m : SheafOfModules.free I ⟶ F) :
    SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ (Scheme.Modules.pullback q).obj F :=
  (pullbackFreeIso q I).inv ≫ (Scheme.Modules.pullback q).map m

theorem pullbackFreeMap_def (q : Y ⟶ X) {F : X.Modules} (m : SheafOfModules.free I ⟶ F) :
    pullbackFreeMap q m = (pullbackFreeIso q I).inv ≫ (Scheme.Modules.pullback q).map m :=
  rfl

/-- The pullback isomorphisms of a free sheaf respect composition (inverse form). -/
@[reassoc]
theorem pullbackFreeIso_inv_comp (p : Z ⟶ Y) (q : Y ⟶ X) (I : Type u) :
    (pullbackFreeIso p I).inv ≫ (Scheme.Modules.pullback p).map (pullbackFreeIso q I).inv ≫
        (pullbackComp p q).hom.app (SheafOfModules.free I) =
      (pullbackFreeIso (p ≫ q) I).inv := by
  rw [← cancel_mono (pullbackFreeIso (p ≫ q) I).hom, Category.assoc, Category.assoc,
    pullbackFreeIso_comp, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Iso.inv_hom_id]

/-- `pullbackFreeMap` respects composition of morphisms. -/
@[reassoc]
theorem pullbackFreeMap_comp (p : Z ⟶ Y) (q : Y ⟶ X) {F : X.Modules}
    (m : SheafOfModules.free I ⟶ F) :
    pullbackFreeMap p (pullbackFreeMap q m) ≫ (pullbackComp p q).hom.app F =
      pullbackFreeMap (p ≫ q) m := by
  have hn := (pullbackComp p q).hom.naturality m
  dsimp only [Functor.comp_map] at hn
  rw [pullbackFreeMap_def, pullbackFreeMap_def, pullbackFreeMap_def,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, hn,
    pullbackFreeIso_inv_comp_assoc]

/-- `pullbackFreeMap` respects equality of morphisms. -/
theorem pullbackFreeMap_congr {q q' : Y ⟶ X} (h : q = q') {F : X.Modules}
    (m : SheafOfModules.free I ⟶ F) :
    pullbackFreeMap q m ≫ (pullbackCongr h).hom.app F = pullbackFreeMap q' m := by
  subst h
  simp [pullbackFreeMap, pullbackCongr]

/-- `pullbackFreeMap` of a composite. -/
theorem pullbackFreeMap_comp_right (q : Y ⟶ X) {F G : X.Modules}
    (m : SheafOfModules.free I ⟶ F) (k : F ⟶ G) :
    pullbackFreeMap q (m ≫ k) = pullbackFreeMap q m ≫ (Scheme.Modules.pullback q).map k := by
  rw [pullbackFreeMap_def, pullbackFreeMap_def, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The pullback of a basis inclusion of a free sheaf, through `pullbackFreeIso`. -/
@[reassoc]
theorem pullback_map_ιFree_comp_pullbackFreeIso_hom (q : Y ⟶ X) (i : I) :
    (Scheme.Modules.pullback q).map (SheafOfModules.ιFree i) ≫ (pullbackFreeIso q I).hom =
      (pullbackUnitIso q).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i

/-- A basis inclusion followed by the inverse of `pullbackFreeIso`. -/
@[reassoc]
theorem ιFree_comp_pullbackFreeIso_inv (q : Y ⟶ X) (i : I) :
    SheafOfModules.ιFree i ≫ (pullbackFreeIso q I).inv =
      (pullbackUnitIso q).inv ≫ (Scheme.Modules.pullback q).map (SheafOfModules.ιFree i) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← pullback_map_ιFree_comp_pullbackFreeIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
