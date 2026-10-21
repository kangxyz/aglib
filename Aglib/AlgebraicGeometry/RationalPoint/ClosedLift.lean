/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Closed-subscheme lifts and rational points of pullbacks

Closed-immersion field-point lift and exact rational point/pullback point comparisons are general
scheme geometry.

Source: `R5Lab.Aglib.AlgebraicGeometry.RationalPoints.ClosedLift`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1ab6e79c642de167b7ba14424d6e713dbcf62d8fa8204f22a0e2519ef75a7449`. Selected lines: [[28, 110]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.RationalPoint

/-- A field-valued point whose image lies in an actual closed subscheme factors
through that subscheme over the SAME field. This uses the actual closed pullback
over Spec K and reducedness of the field, not a supplied residue-field map. -/
theorem closedImmersion_fieldPoint_lift {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (K : Type u) [Field K] (p : Spec (.of K) ⟶ Y)
    (hp : p default ∈ Set.range i) :
    ∃ s : Spec (.of K) ⟶ X, s ≫ i = p := by
  let : Surjective (pullback.snd i p) := ⟨by
    intro x
    change x ∈ Set.range (pullback.snd i p)
    rw [Scheme.Pullback.range_snd]
    change p x ∈ Set.range i
    have hx : x = default := Subsingleton.elim _ _
    simpa only [hx] using hp⟩
  let : IsIso (pullback.snd i p) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.snd i p) ≫ pullback.fst i p, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The lift preserves any actual field structure carried by the original
point and the closed immersion. -/
theorem closedImmersion_rationalPoint_lift {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (K : Type u) [Field K] (q : Y ⟶ Spec (.of K))
    (p : Spec (.of K) ⟶ Y) (hp : p default ∈ Set.range i) (hpoint : p ≫ q = 𝟙 _) :
    ∃ s : Spec (.of K) ⟶ X, s ≫ i = p ∧ s ≫ (i ≫ q) = 𝟙 _ := by
  obtain ⟨s, hs⟩ := closedImmersion_fieldPoint_lift i K p hp
  exact ⟨s, hs, by rw [← Category.assoc, hs, hpoint]⟩

/-- Original-field sections with the same actual point agree as morphisms. No
algebraic-closure hypothesis is needed. -/
theorem rationalPoint_eq_of_apply_eq {X : Scheme.{u}} (k : Type u) [Field k]
    (s : X ⟶ Spec (.of k)) (p q : Spec (.of k) ⟶ X)
    (hp : p ≫ s = 𝟙 _) (hq : q ≫ s = 𝟙 _) (he : p default = q default) : p = q := by
  let : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id s p hp
  obtain ⟨r, hr⟩ := closedImmersion_fieldPoint_lift p k q ⟨default, he⟩
  have hri : r = 𝟙 _ := by
    calc
      r = r ≫ p ≫ s := by rw [hp, Category.comp_id]
      _ = q ≫ s := by rw [← Category.assoc, hr]
      _ = 𝟙 _ := hq
  simpa [hri] using hr

/-- A prescribed actual point of a pullback whose two projections are rational
is itself rational, with the original projections retained exactly. This does
not assume the whole morphism is injective, and therefore applies at a
self-node of a one-gon as well as at intersections of distinct components. -/
theorem pullback_rationalPoint_at {X Y B : Scheme.{u}} (k : Type u) [Field k]
    (f : X ⟶ B) (g : Y ⟶ B) (s : B ⟶ Spec (.of k))
    (p : Spec (.of k) ⟶ X) (q : Spec (.of k) ⟶ Y)
    (hp : p ≫ f ≫ s = 𝟙 _) (hq : q ≫ g ≫ s = 𝟙 _)
    (t : ↑(pullback f g))
    (htp : pullback.fst f g t = p default)
    (htq : pullback.snd f g t = q default) :
    ∃ r : Spec (.of k) ⟶ pullback f g,
      r default = t ∧ r ≫ pullback.fst f g = p ∧ r ≫ pullback.snd f g = q := by
  have he : p ≫ f = q ≫ g := by
    apply rationalPoint_eq_of_apply_eq k s _ _ (by simpa using hp) (by simpa using hq)
    simp only [Scheme.Hom.comp_apply]
    rw [← htp, ← htq]
    exact congrArg (fun h : pullback f g ⟶ B => h t) (pullback.condition (f := f) (g := g))
  let h : Spec (.of k) ⟶ B := p ≫ f
  let : IsClosedImmersion h := isClosedImmersion_of_comp_eq_id s h (by simpa [h] using hp)
  let j : pullback h h ⟶ pullback f g :=
    pullback.map h h f g p q (𝟙 _) (by simp [h]) (by simpa [h] using he)
  have ht : t ∈ Set.range j := by
    dsimp only [j]
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨default, htp.symm⟩, ⟨default, htq.symm⟩⟩
  obtain ⟨v, hv⟩ := ht
  let r : Spec (.of k) ⟶ pullback f g := inv (pullback.fst h h) ≫ j
  have hr : r default = t := by
    dsimp only [r]
    rw [Scheme.Hom.comp_apply]
    have hv' : inv (pullback.fst h h) default = v := by
      apply (pullback.fst h h).homeomorph.injective
      have hid := congrArg (fun a : Spec (.of k) ⟶ Spec (.of k) => a default)
        (IsIso.inv_hom_id (pullback.fst h h))
      change pullback.fst h h (inv (pullback.fst h h) default) = _
      exact hid.trans (Subsingleton.elim _ _)
    rw [hv', hv]
  have hrp : r ≫ pullback.fst f g = p := by
    simp [r, j]
  have hrq : r ≫ pullback.snd f g = q := by
    simp only [r, j, Category.assoc, pullback.lift_snd]
    rw [← fst_eq_snd_of_mono_eq, IsIso.inv_hom_id_assoc]
  exact ⟨r, hr, hrp, hrq⟩

/-- Actual rational sections with equal scheme points agree, retaining both section triangles. -/
lemma rationalSection_ext {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (p q : Spec (.of k) ⟶ X)
    (hp : p ≫ s = 𝟙 _) (hq : q ≫ s = 𝟙 _)
    (hpoint : p (IsLocalRing.closedPoint k) = q (IsLocalRing.closedPoint k)) : p = q := by
  apply rationalPoint_eq_of_apply_eq k s p q hp hq
  simpa only [show (default : Spec (.of k)) = IsLocalRing.closedPoint k from
    Subsingleton.elim _ _] using hpoint

end AlgebraicGeometry.Scheme.RationalPoint
