/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLimits

/-! # Original sections lifted by finite-etale fullness

The source is the native identity cover. The resulting scheme section retains
both its structural equation and its specified base-change equation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

/-- Fullness of the original finite-etale pullback lifts an actual section,
with the original prescribed triangle rather than only an isomorphism class. -/
theorem exists_section_of_baseChange_full
    {X S : Scheme.{u}} (f : S ⟶ X) [(baseChange f).Full]
    (C : FiniteEtale X) (a : S ⟶ C.obj.left) (ha : a ≫ C.obj.hom = f) :
    ∃ s : X ⟶ C.obj.left, s ≫ C.obj.hom = 𝟙 X ∧ f ≫ s = a := by
  let l : pullback (𝟙 X) f ⟶ pullback C.obj.hom f :=
    pullback.lift (pullback.snd (𝟙 X) f ≫ a) (pullback.snd (𝟙 X) f)
      (by rw [Category.assoc, ha])
  let t : (baseChange f).obj (terminalCover X) ⟶ (baseChange f).obj C :=
    ObjectProperty.homMk (Over.homMk l (pullback.lift_snd ..))
  obtain ⟨s, hs⟩ := (baseChange f).map_surjective t
  refine ⟨s.hom.left, s.hom.w, ?_⟩
  have hfst : pullback.fst (𝟙 X) f ≫ s.hom.left =
      pullback.snd (𝟙 X) f ≫ a := by
    calc
      _ = ((baseChange f).map s).hom.left ≫ pullback.fst C.obj.hom f :=
        (pullback.lift_fst ..).symm
      _ = t.hom.left ≫ pullback.fst C.obj.hom f := by rw [hs]
      _ = _ := pullback.lift_fst ..
  let i : S ⟶ pullback (𝟙 X) f := pullback.lift f (𝟙 S) (by simp)
  have hi := congrArg (fun k => i ≫ k) hfst
  simpa only [i, ← Category.assoc, pullback.lift_fst, pullback.lift_snd,
    Category.id_comp] using hi

end AlgebraicGeometry.Scheme.FiniteEtale
