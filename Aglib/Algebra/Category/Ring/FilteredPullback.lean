/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Pulling a filtered ring colimit back along a fixed ring map

For an actual filtered colimit `R = colim Rᵢ` and a map `B → R`, the rings
`B ×[R] Rᵢ` form a filtered diagram with colimit literally `B`. The objects,
transition maps, and cartesian squares are the native categorical pullbacks.
No injectivity, surjectivity, finite presentation, or flatness is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat.FilteredPullback

universe u

variable {I : Type u} [Category.{u} I] {F : I ⥤ CommRingCat.{u}}
variable (c : Cocone F) {B : CommRingCat.{u}} (s : B ⟶ c.pt)

/-- The diagram of the actual ring pullbacks of the colimit structure maps. -/
def ringDiagram : I ⥤ CommRingCat.{u} where
  obj i := pullback s (c.ι.app i)
  map {i j} f := pullback.map s (c.ι.app i) s (c.ι.app j)
    (𝟙 B) (F.map f) (𝟙 c.pt) (by simp) (by simp)
  map_id i := by
    apply pullback.hom_ext <;> simp [pullback.map]
  map_comp f g := by
    apply pullback.hom_ext <;>
      simp [pullback.map, Functor.map_comp, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc]

@[reassoc (attr := simp)]
lemma ringDiagram_map_fst {i j : I} (f : i ⟶ j) :
    (ringDiagram c s).map f ≫ pullback.fst s (c.ι.app j) =
      pullback.fst s (c.ι.app i) := by
  simp [ringDiagram, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma ringDiagram_map_snd {i j : I} (f : i ⟶ j) :
    (ringDiagram c s).map f ≫ pullback.snd s (c.ι.app j) =
      pullback.snd s (c.ι.app i) ≫ F.map f := by
  simp [ringDiagram, pullback.map, pullback.lift_snd]

@[simp]
lemma ringDiagram_map_fst_apply {i j : I} (f : i ⟶ j)
    (x : (pullback s (c.ι.app i) : CommRingCat.{u})) :
    (pullback.fst s (c.ι.app j)).hom (((ringDiagram c s).map f).hom x) =
      (pullback.fst s (c.ι.app i)).hom x :=
  congrArg (fun q : pullback s (c.ι.app i) ⟶ B ↦ q.hom x)
    (ringDiagram_map_fst c s f)

@[simp]
lemma ringDiagram_map_snd_apply {i j : I} (f : i ⟶ j)
    (x : (pullback s (c.ι.app i) : CommRingCat.{u})) :
    (pullback.snd s (c.ι.app j)).hom (((ringDiagram c s).map f).hom x) =
      (F.map f).hom ((pullback.snd s (c.ι.app i)).hom x) :=
  congrArg (fun q : pullback s (c.ι.app i) ⟶ F.obj j ↦ q.hom x)
    (ringDiagram_map_snd c s f)

/-- The first projections form a cocone with point the prescribed ring. -/
def ringCocone : Cocone (ringDiagram c s) where
  pt := B
  ι :=
    { app i := pullback.fst s (c.ι.app i)
      naturality i j f := by
        change (ringDiagram c s).map f ≫ pullback.fst s (c.ι.app j) =
          pullback.fst s (c.ι.app i) ≫ 𝟙 B
        rw [Category.comp_id, ringDiagram_map_fst] }

/-- The second projections form a map to the original ring diagram. -/
def toOriginal : ringDiagram c s ⟶ F where
  app i := pullback.snd s (c.ι.app i)
  naturality _ _ f := ringDiagram_map_snd c s f

/-- Each stage is the native cartesian square over the original colimit. -/
theorem isPullback (i : I) :
    IsPullback ((ringCocone c s).ι.app i) ((toOriginal c s).app i) s (c.ι.app i) :=
  .of_hasPullback s (c.ι.app i)

variable [IsFiltered I]

/-- The first projections exhibit `B` as the filtered colimit of the pullbacks. -/
def ringCoconeIsColimit (hc : IsColimit c) : IsColimit (ringCocone c s) := by
  let hcT := isColimitOfPreserves (forget CommRingCat.{u}) hc
  let : ReflectsColimit (ringDiagram c s) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro b
    obtain ⟨i, r, hr⟩ := Types.jointly_surjective_of_isColimit hcT (s.hom b)
    obtain ⟨x, hx, -⟩ := Types.exists_of_isPullback
      ((forget CommRingCat.{u}).map_isPullback (isPullback c s i)) b r hr.symm
    exact ⟨i, x, hx.symm⟩
  · intro i x y h
    change (pullback.fst s (c.ι.app i)).hom x =
      (pullback.fst s (c.ι.app i)).hom y at h
    have he : (c.ι.app i).hom ((pullback.snd s (c.ι.app i)).hom x) =
        (c.ι.app i).hom ((pullback.snd s (c.ι.app i)).hom y) := by
      have hx := congrArg (fun f : pullback s (c.ι.app i) ⟶ c.pt ↦ f.hom x)
        (pullback.condition (f := s) (g := c.ι.app i))
      have hy := congrArg (fun f : pullback s (c.ι.app i) ⟶ c.pt ↦ f.hom y)
        (pullback.condition (f := s) (g := c.ι.app i))
      exact hx.symm.trans ((congrArg s.hom h).trans hy)
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcT _ _).mp he
    refine ⟨j, f, Types.ext_of_isPullback
      ((forget CommRingCat.{u}).map_isPullback (isPullback c s j)) ?_ ?_⟩
    · change (pullback.fst s (c.ι.app j)).hom (((ringDiagram c s).map f).hom x) =
        (pullback.fst s (c.ι.app j)).hom (((ringDiagram c s).map f).hom y)
      exact (ringDiagram_map_fst_apply c s f x).trans
        (h.trans (ringDiagram_map_fst_apply c s f y).symm)
    · change (pullback.snd s (c.ι.app j)).hom (((ringDiagram c s).map f).hom x) =
        (pullback.snd s (c.ι.app j)).hom (((ringDiagram c s).map f).hom y)
      exact (ringDiagram_map_snd_apply c s f x).trans
        (hf.trans (ringDiagram_map_snd_apply c s f y).symm)

end CommRingCat.FilteredPullback
