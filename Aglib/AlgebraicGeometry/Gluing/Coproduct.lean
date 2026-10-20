/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Open pushouts and binary coproducts

Source: `R5Lab.Aglib.AlgebraicGeometry.Gluing.Coproduct`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `0b168f4cd9d7a79a6b5b28e52677ae1b23cb581ef560e82a214da34f112c9578`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.OpenPushout

variable {W U V : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
variable [IsOpenImmersion f] [IsOpenImmersion g]

/-- The morphism from the pushout of doubled open charts to the coproduct of two copies of their
pushout. -/
def doublePushoutHom : pushout (coprod.map f f) (coprod.map g g) ⟶
    (pushout f g ⨿ pushout f g) :=
  pushout.desc (coprod.map (pushout.inl f g) (pushout.inl f g))
    (coprod.map (pushout.inr f g) (pushout.inr f g)) (by
      apply coprod.hom_ext <;>
        simp only [coprod.inl_map_assoc, coprod.inr_map_assoc,
          coprod.inl_map, coprod.inr_map]
      all_goals simp only [← Category.assoc, pushout.condition])

/-- The morphism from the coproduct of two open pushouts to the pushout of the doubled charts. -/
def doublePushoutInv : (pushout f g ⨿ pushout f g) ⟶
    pushout (coprod.map f f) (coprod.map g g) :=
  coprod.desc
    (pushout.desc (coprod.inl ≫ pushout.inl (coprod.map f f) (coprod.map g g))
      (coprod.inl ≫ pushout.inr (coprod.map f f) (coprod.map g g)) (by
        simpa only [coprod.inl_map_assoc, Category.assoc] using
          congrArg ((coprod.inl : W ⟶ W ⨿ W) ≫ ·)
            (pushout.condition (f := coprod.map f f) (g := coprod.map g g))))
    (pushout.desc (coprod.inr ≫ pushout.inl (coprod.map f f) (coprod.map g g))
      (coprod.inr ≫ pushout.inr (coprod.map f f) (coprod.map g g)) (by
        simpa only [coprod.inr_map_assoc, Category.assoc] using
          congrArg ((coprod.inr : W ⟶ W ⨿ W) ≫ ·)
            (pushout.condition (f := coprod.map f f) (g := coprod.map g g))))

/-- The isomorphism expressing the pushout of doubled open charts as two copies of the original
pushout. -/
def doublePushoutIso : pushout (coprod.map f f) (coprod.map g g) ≅
    (pushout f g ⨿ pushout f g) where
  hom := doublePushoutHom f g
  inv := doublePushoutInv f g
  hom_inv_id := by
    apply pushout.hom_ext <;> apply coprod.hom_ext <;>
      simp [doublePushoutHom, doublePushoutInv]
  inv_hom_id := by
    apply coprod.hom_ext <;> apply pushout.hom_ext <;>
      simp [doublePushoutHom, doublePushoutInv, Category.assoc]

/-- A disjoint union of two proper schemes remains proper, via a finite fold map. -/
theorem coprodDesc_proper {X S : Scheme.{u}} (p : X ⟶ S) [IsProper p] :
    IsProper (coprod.desc p p) := by
  have : IsProper (coprod.map p p) :=
    IsZariskiLocalAtTarget.coprodMap p p inferInstance inferInstance
  have he : coprod.desc p p = coprod.map p p ≫ coprod.desc (𝟙 S) (𝟙 S) := by
    apply coprod.hom_ext <;> simp
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.OpenPushout
