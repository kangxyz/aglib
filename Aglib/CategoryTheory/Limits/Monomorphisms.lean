/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Cofiltered limits of monomorphisms and cartesian diagonals

Projections from a cofiltered limit of monomorphisms are monomorphisms.
A monomorphism over a fixed base induces a cartesian square of the original
relative diagonals. These categorical suppliers are used for eventual
separatedness of schemes with closed-immersion transitions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v u vI uI

variable {C : Type u} [Category.{v} C]

/-- Every projection from a cofiltered limit of monomorphisms is monic. -/
theorem IsLimit.mono_π_app {I : Type uI} [Category.{vI} I] [IsCofilteredOrEmpty I]
    (D : I ⥤ C) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (q : i ⟶ j), Mono (D.map q)] (i : I) : Mono (c.π.app i) := by
  constructor
  intro Z f g hfg
  apply hc.hom_ext
  intro j
  obtain ⟨k, ki, kj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  have hfg' : f ≫ c.π.app k = g ≫ c.π.app k := by
    apply (cancel_mono (D.map ki)).mp
    simpa only [Category.assoc, Cone.w] using hfg
  rw [← c.w kj, ← Category.assoc, hfg', Category.assoc]

/-- Relative diagonals form a cartesian square under a monomorphism over
the base. The lower map is the original map between native pullbacks. -/
theorem isPullback_diagonal_of_mono [HasPullbacks C]
    {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S)
    (q : X ⟶ Y) (hq : q ≫ g = f) [Mono q] :
    IsPullback q (pullback.diagonal f) (pullback.diagonal g)
      (pullback.map f f g g q q (𝟙 S)
        (by simpa using hq.symm) (by simpa using hq.symm)) := by
  let a := pullback.map f f g g q q (𝟙 S)
    (by simpa using hq.symm) (by simpa using hq.symm)
  have hw : q ≫ pullback.diagonal g = pullback.diagonal f ≫ a := by
    apply pullback.hom_ext <;> simp [a, pullback.map]
  refine ⟨⟨hw⟩, ⟨PullbackCone.isLimitAux' _ (fun s ↦ ?_)⟩⟩
  have hfst : (s.snd ≫ pullback.fst f f) ≫ q = s.fst := by
    have h := congrArg (fun m ↦ m ≫ pullback.fst g g) s.condition
    simpa [a, pullback.map] using h.symm
  have hsnd : (s.snd ≫ pullback.snd f f) ≫ q = s.fst := by
    have h := congrArg (fun m ↦ m ≫ pullback.snd g g) s.condition
    simpa [a, pullback.map] using h.symm
  have heq : s.snd ≫ pullback.fst f f = s.snd ≫ pullback.snd f f := by
    exact (cancel_mono q).mp (hfst.trans hsnd.symm)
  have hdiag : (s.snd ≫ pullback.fst f f) ≫ pullback.diagonal f = s.snd := by
    apply pullback.hom_ext
    · simp
    · simpa using heq
  refine ⟨s.snd ≫ pullback.fst f f, hfst, hdiag, ?_⟩
  intro m _ hm
  apply (cancel_mono (pullback.diagonal f)).mp
  exact hm.trans hdiag.symm

end CategoryTheory.Limits
