/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.GenericExtension
public import Aglib.AlgebraicGeometry.Stalk.GenericSection
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Lifting the original section through a proper trait morphism

If the original native generic-fibre map of a proper morphism is an
isomorphism, every original section of its target lifts uniquely. The
generic lift uses the inverse of that same native map. The native proper
valuative criterion supplies the extension over the original DVR and its
specified fraction field. Every possible section lift has the same
generic restriction, so uniqueness applies to the original section.
The exact base, projection and generic-section equations are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.LocalRing.GenericFiber (baseMap)

universe u

namespace AlgebraicGeometry.Scheme.ProperTraitSections

variable (R F : Type u) [CommRing R] [Field F] [Algebra R F]
  {X Y : Scheme.{u}} (p : X ⟶ Spec (.of R)) (f : Y ⟶ X)

private theorem genericMap_fst :
    ((Over.pullback (baseMap R F)).map
      (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)).left ≫
        pullback.fst p (baseMap R F) = pullback.fst (f ≫ p) (baseMap R F) ≫ f := by
  simp [Over.pullback_map_left]

/-- The literal generic sections retain any given original section triangle. -/
theorem genericSection_comp_genericMap (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ f = s) :
    GenericSection.genericSection R F (f ≫ p) t
        (by rw [← Category.assoc, ht, hs]) ≫
      ((Over.pullback (baseMap R F)).map
        (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)).left =
      GenericSection.genericSection R F p s hs := by
  apply pullback.hom_ext
  · simp [GenericSection.genericSection, Over.pullback_map_left, Category.assoc, ht]
  · simp [GenericSection.genericSection, Over.pullback_map_left]

variable [hGeneric : IsIso ((Over.pullback (baseMap R F)).map
  (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p))]

/-- The original generic section lifted by the inverse of the specified
native generic-fibre map, on the original literal source fibre. -/
def genericSectionLift (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    Spec (.of F) ⟶ pullback (f ≫ p) (baseMap R F) :=
  GenericSection.genericSection R F p s hs ≫
    (inv ((Over.pullback (baseMap R F)).map
      (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p))).left

/-- The actual generic map into the original source of the proper morphism. -/
def genericLift (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) : Spec (.of F) ⟶ Y :=
  genericSectionLift R F p f s hs ≫ pullback.fst (f ≫ p) (baseMap R F)

@[reassoc]
theorem genericSectionLift_comp_genericMap (s : Spec (.of R) ⟶ X)
    (hs : s ≫ p = 𝟙 _) :
    genericSectionLift R F p f s hs ≫
      ((Over.pullback (baseMap R F)).map
        (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)).left =
      GenericSection.genericSection R F p s hs := by
  let m := (Over.pullback (baseMap R F)).map
    (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)
  have hi : (inv m).left ≫ m.left =
      𝟙 (pullback (C := Scheme.{u}) p (baseMap R F)) :=
    ((Over.forget (Spec (.of F))).mapIso (asIso m)).inv_hom_id
  change (GenericSection.genericSection R F p s hs ≫ (inv m).left) ≫ m.left = _
  rw [Category.assoc, hi]
  exact Category.comp_id _

/-- The inverse generic map preserves the original structural map to Spec F. -/
@[reassoc]
theorem genericSectionLift_structure (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    genericSectionLift R F p f s hs ≫ pullback.snd (f ≫ p) (baseMap R F) = 𝟙 _ := by
  let m := (Over.pullback (baseMap R F)).map
    (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)
  have hm : (inv m).left ≫ pullback.snd (f ≫ p) (baseMap R F) =
      pullback.snd p (baseMap R F) := (inv m).w
  change (GenericSection.genericSection R F p s hs ≫ (inv m).left) ≫ _ = _
  rw [Category.assoc, hm]
  exact GenericSection.genericSection_structure R F p s hs

/-- The generic lift maps to the same original generic restriction of the section. -/
@[reassoc]
theorem genericLift_comp (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    genericLift R F p f s hs ≫ f = baseMap R F ≫ s := by
  unfold genericLift
  rw [Category.assoc, ← genericMap_fst R F p f, ← Category.assoc,
    genericSectionLift_comp_genericMap, GenericSection.genericSection_projection]

/-- Every lift of the original section has the prescribed literal generic section. -/
theorem genericSection_eq_genericSectionLift (s : Spec (.of R) ⟶ X)
    (hs : s ≫ p = 𝟙 _) (t : Spec (.of R) ⟶ Y) (ht : t ≫ f = s) :
    GenericSection.genericSection R F (f ≫ p) t
        (by rw [← Category.assoc, ht, hs]) = genericSectionLift R F p f s hs := by
  let m := (Over.pullback (baseMap R F)).map
    (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)
  have : IsIso m.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of F))).map m))
  apply (cancel_mono m.left).mp
  exact (genericSection_comp_genericMap R F p f s hs t ht).trans
    (genericSectionLift_comp_genericMap R F p f s hs).symm

/-- Any original section lift has the original prescribed generic restriction. -/
theorem baseMap_comp_eq_genericLift (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ f = s) :
    baseMap R F ≫ t = genericLift R F p f s hs := by
  have htp : t ≫ (f ≫ p) = 𝟙 _ := by rw [← Category.assoc, ht, hs]
  calc
    baseMap R F ≫ t = GenericSection.genericSection R F (f ≫ p) t htp ≫
        pullback.fst (f ≫ p) (baseMap R F) :=
      (GenericSection.genericSection_projection R F (f ≫ p) t htp).symm
    _ = genericSectionLift R F p f s hs ≫ pullback.fst (f ≫ p) (baseMap R F) :=
      congrArg (fun a : Spec (.of F) ⟶ pullback (C := Scheme.{u}) (f ≫ p) (baseMap R F) =>
        a ≫ pullback.fst (f ≫ p) (baseMap R F))
        (genericSection_eq_genericSectionLift R F p f s hs t ht)
    _ = genericLift R F p f s hs := rfl

variable [IsDomain R] [IsDiscreteValuationRing R] [hFrac : IsFractionRing R F] [IsProper f]

include hGeneric hFrac

/-- A proper morphism whose original native generic-fibre map is invertible
lifts the original trait section uniquely. No condition on the target
structural morphism, other than the supplied section, is required. -/
theorem existsUnique_lift (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    ∃! t : Spec (.of R) ⟶ Y, t ≫ f = s := by
  let g := genericLift R F p f s hs
  let sq : ValuativeCommSq f := {
    R := R
    K := F
    i₁ := g
    i₂ := s
    commSq := ⟨genericLift_comp R F p f s hs⟩ }
  have hval : ValuativeCriterion f := by
    have hf : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hf
    exact hf.1.1.1
  obtain ⟨U⟩ := hval sq
  let L : sq.commSq.LiftStruct := U.default
  refine ⟨L.l, L.fac_right, ?_⟩
  intro t ht
  let Lt : sq.commSq.LiftStruct := {
    l := t
    fac_left := baseMap_comp_eq_genericLift R F p f s hs t ht
    fac_right := ht }
  exact congrArg CommSq.LiftStruct.l (U.uniq Lt)

/-- The unique lift of the original section, obtained from the original
native generic inverse and the proper valuative criterion. -/
def lift (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) : Spec (.of R) ⟶ Y :=
  (existsUnique_lift R F p f s hs).choose

@[reassoc (attr := simp)]
theorem lift_comp (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    lift R F p f s hs ≫ f = s :=
  (existsUnique_lift R F p f s hs).choose_spec.1

/-- The lifted map is a section of the original composite structural morphism. -/
@[reassoc]
theorem lift_toBase (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    lift R F p f s hs ≫ (f ≫ p) = 𝟙 _ := by
  rw [← Category.assoc, lift_comp, hs]

theorem lift_unique (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (t : Spec (.of R) ⟶ Y) (ht : t ≫ f = s) : t = lift R F p f s hs :=
  (existsUnique_lift R F p f s hs).choose_spec.2 t ht

/-- The original generic restriction of the unique lift is the prescribed generic map. -/
@[reassoc (attr := simp)]
theorem lift_generic (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    baseMap R F ≫ lift R F p f s hs = genericLift R F p f s hs :=
  baseMap_comp_eq_genericLift R F p f s hs (lift R F p f s hs) (lift_comp R F p f s hs)

/-- The literal generic section of the unique lift is the original section
composed with the inverse of the given native generic-fibre map. -/
theorem lift_genericSection (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    GenericSection.genericSection R F (f ≫ p) (lift R F p f s hs)
        (lift_toBase R F p f s hs) =
      GenericSection.genericSection R F p s hs ≫
        (inv ((Over.pullback (baseMap R F)).map
          (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p))).left :=
  genericSection_eq_genericSectionLift R F p f s hs
    (lift R F p f s hs) (lift_comp R F p f s hs)

/-- Under the original forward generic map, the lifted literal section is the original one. -/
@[reassoc]
theorem lift_genericSection_comp (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    GenericSection.genericSection R F (f ≫ p) (lift R F p f s hs)
        (lift_toBase R F p f s hs) ≫
      ((Over.pullback (baseMap R F)).map
        (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)).left =
      GenericSection.genericSection R F p s hs :=
  genericSection_comp_genericMap R F p f s hs (lift R F p f s hs) (lift_comp R F p f s hs)

end AlgebraicGeometry.Scheme.ProperTraitSections
