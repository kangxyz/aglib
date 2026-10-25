/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Pointed étale neighborhoods inside an étale monomorphism

Postcomposition along an étale monomorphism containing the marked geometric
point is initial on the original categories of pointed étale neighborhoods.
The opposite functor is therefore final for the original stalk diagrams.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtalePointOpen

universe u

variable {U S : Scheme.{u}} (j : U ⟶ S) [Etale j]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ηU : Spec (.of Ω) ⟶ U) (η : Spec (.of Ω) ⟶ S) (hη : ηU ≫ j = η)

local instance etaleStable : MorphismProperty.IsStableUnderComposition
    (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ Etale f) where
  comp_mem f g hf hg := by
    let : Etale f := hf
    let : Etale g := hg
    infer_instance

/-- Postcomposition of the underlying original small étale objects. -/
abbrev postcompose : U.Etale ⥤ S.Etale :=
  MorphismProperty.Over.map (f := j)
    (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ Etale f) ⊤
    (show Etale j from inferInstance)

/-- The marked point is unchanged as a scheme map. -/
def postcomposePoint (d : (pointSmallEtale ηU).fiber.Elements) :
    (pointSmallEtale η).fiber.obj ((postcompose j).obj d.obj) :=
  Over.homMk d.val.left (by
    change d.val.left ≫ (d.obj.hom ≫ j) = η
    exact (Category.assoc d.val.left d.obj.hom j).symm.trans
      ((congrArg (fun a : Spec (.of Ω) ⟶ U => a ≫ j) (Over.w d.val)).trans hη))

/-- The native pointed-neighborhood functor induced by an étale map. -/
def toPointElements : (pointSmallEtale ηU).fiber.Elements ⥤
    (pointSmallEtale η).fiber.Elements where
  obj d := Functor.elementsMk _ ((postcompose j).obj d.obj)
    (postcomposePoint j ηU η hη d)
  map {d e} f :=
    { hom := (postcompose j).map f.hom
      map_val := by
        apply Over.OverMorphism.ext
        have hp := congrArg
          (fun k : Over.mk ηU ⟶ (Etale.forget U).obj e.obj => k.left) f.map_val
        exact hp }
  map_id d := by
    apply Functor.Elements.Hom.ext
    exact (postcompose j).map_id d.obj
  map_comp f g := by
    apply Functor.Elements.Hom.ext
    exact (postcompose j).map_comp f.hom g.hom

@[simp]
lemma toPointElements_obj_obj (d : (pointSmallEtale ηU).fiber.Elements) :
    ((toPointElements j ηU η hη).obj d).obj = (postcompose j).obj d.obj := rfl

@[simp]
lemma toPointElements_obj_point (d : (pointSmallEtale ηU).fiber.Elements) :
    ((toPointElements j ηU η hη).obj d).val.left = d.val.left := rfl

@[simp]
lemma toPointElements_map_left {d e : (pointSmallEtale ηU).fiber.Elements} (f : d ⟶ e) :
    ((toPointElements j ηU η hη).map f).hom.left = f.hom.left := rfl

instance : (toPointElements j ηU η hη).Faithful where
  map_injective {d e} f g h := by
    apply Functor.Elements.Hom.ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun k => k.hom.left) h

variable [Mono j]

instance : (toPointElements j ηU η hη).Full where
  map_surjective {d e} f := by
    have hw : f.hom.left ≫ e.obj.hom = d.obj.hom := by
      apply (cancel_mono j).mp
      exact (Category.assoc _ _ _).trans (MorphismProperty.Over.w f.hom)
    let a : d.obj ⟶ e.obj := MorphismProperty.Over.homMk f.hom.left hw
    have hp : (pointSmallEtale ηU).fiber.map a d.val = e.val := by
      apply Over.OverMorphism.ext
      have hp := congrArg
        (fun k : Over.mk η ⟶ (Etale.forget S).obj
          ((toPointElements j ηU η hη).obj e).obj => k.left) f.map_val
      exact hp
    refine ⟨{ hom := a, map_val := hp }, ?_⟩
    apply Functor.Elements.Hom.ext
    apply MorphismProperty.Over.Hom.ext
    rfl

omit [Mono j] in
/-- An original pointed neighborhood receives the actual pullback neighborhood.
The two projections retain respectively the original point and the lifted base point. -/
theorem exists_pointed_refinement (d : (pointSmallEtale η).fiber.Elements) :
    ∃ e : (pointSmallEtale ηU).fiber.Elements,
      Nonempty ((toPointElements j ηU η hη).obj e ⟶ d) := by
  let : Etale d.obj.hom := d.obj.prop
  obtain ⟨y, hy, hyEq⟩ := Over.homMk_surjective d.val
  let W : U.Etale := Scheme.Etale.mk (pullback.snd d.obj.hom j)
  let p : Spec (.of Ω) ⟶ pullback d.obj.hom j :=
    pullback.lift y ηU (hy.trans hη.symm)
  have hp : p ≫ pullback.snd d.obj.hom j = ηU := pullback.lift_snd _ _ _
  let e := Functor.elementsMk (pointSmallEtale ηU).fiber W (Over.homMk p hp)
  refine ⟨e, ⟨?_⟩⟩
  refine
    { hom := MorphismProperty.Over.homMk (pullback.fst d.obj.hom j)
        (pullback.condition (f := d.obj.hom) (g := j))
      map_val := ?_ }
  apply Over.OverMorphism.ext
  exact (pullback.lift_fst y ηU (hy.trans hη.symm)).trans
    (congrArg Over.Hom.left hyEq).symm

/-- Pointed neighborhoods contained in the étale monomorphism are initial in
all original pointed neighborhoods. No base-change theorem is used. -/
instance toPointElements_initial : (toPointElements j ηU η hη).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  exact exists_pointed_refinement j ηU η hη

/-- The opposite native neighborhood functor is final for stalk colimits. -/
instance toPointElements_op_final : (toPointElements j ηU η hη).op.Final := inferInstance

end AlgebraicGeometry.Scheme.EtalePointOpen
