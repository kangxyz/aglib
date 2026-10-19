/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Coherence of the pullback isomorphisms of free module sheaves

Mathlib's `pullbackObjFreeIso`, written `Scheme.Modules.pullbackFreeIso f I :
f^* (free I) ≅ free I`, respects Mathlib's comparisons of pullbacks: composition
(`pullbackFreeIso_comp`, with `pullbackComp f g : g^* ⋙ f^* ≅ (f ≫ g)^*`), identity
(`pullbackFreeIso_id`) and equality of morphisms (`pullbackFreeIso_congr`). The first two are
checked on the summand inclusions `ιFree i`, where they are `pullbackUnitIso_comp` and
`pullbackUnitIso_id`; the third follows by substituting the equality. No hypothesis on the schemes
or the index type.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The pullback isomorphisms of a free sheaf respect composition of scheme morphisms. -/
theorem pullbackFreeIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) (I : Type u) :
    (pullbackComp f g).hom.app (SheafOfModules.free I) ≫ (pullbackFreeIso (f ≫ g) I).hom =
      (pullback f).map (pullbackFreeIso g I).hom ≫ (pullbackFreeIso f I).hom := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback g ⋙ pullback f) _ _
    (SheafOfModules.isColimitFreeCofan (R := Z.ringCatSheaf) I)) _ _ (fun i ↦ ?_)
  have h₁ := (pullbackComp f g).hom.naturality (SheafOfModules.ιFree (R := Z.ringCatSheaf) i)
  dsimp only [Functor.comp_map] at h₁
  change (pullback f).map ((pullback g).map (SheafOfModules.ιFree i)) ≫ _ =
    (pullback f).map ((pullback g).map (SheafOfModules.ιFree i)) ≫ _
  rw [reassoc_of% h₁]
  erw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  erw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom]
  rw [CategoryTheory.Functor.map_comp_assoc]
  erw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom]
  have h₂ := pullbackUnitIso_comp f g
  change _ ≫ SheafOfModules.pullbackObjUnitToUnit _ = (pullback f).map
    (SheafOfModules.pullbackObjUnitToUnit _) ≫ SheafOfModules.pullbackObjUnitToUnit _ at h₂
  rw [← Category.assoc, h₂, Category.assoc]

/-- The pullback isomorphism of a free sheaf along the identity is the identity comparison. -/
theorem pullbackFreeIso_id (X : Scheme.{u}) (I : Type u) :
    (pullbackId X).hom.app (SheafOfModules.free I) = (pullbackFreeIso (𝟙 X) I).hom := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback (𝟙 X)) _ _
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)) _ _ (fun i ↦ ?_)
  have h₁ := (pullbackId X).hom.naturality (SheafOfModules.ιFree (R := X.ringCatSheaf) i)
  dsimp only [Functor.id_map] at h₁
  change (pullback (𝟙 X)).map (SheafOfModules.ιFree i) ≫ _ =
    (pullback (𝟙 X)).map (SheafOfModules.ιFree i) ≫ _
  rw [h₁]
  erw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom]
  have h₂ := pullbackUnitIso_id X
  change _ = SheafOfModules.pullbackObjUnitToUnit _ at h₂
  rw [h₂]

/-- The pullback isomorphisms of a free sheaf along equal morphisms agree. -/
theorem pullbackFreeIso_congr {f g : X ⟶ Y} (h : f = g) (I : Type u) :
    (pullbackCongr h).hom.app (SheafOfModules.free I) ≫ (pullbackFreeIso g I).hom =
      (pullbackFreeIso f I).hom := by
  subst h
  simp [pullbackCongr]

end AlgebraicGeometry.Scheme.Modules
