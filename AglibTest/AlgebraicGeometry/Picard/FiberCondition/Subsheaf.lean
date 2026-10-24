/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.FiberCondition.Subsheaf

/-! Focused consumer of the subsheaf `Pic^C ⊂ Pic_{X/S,(fppf)}` of a fiber condition (Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 28, with fppf in place of étale):
the pointwise condition on sections is independent of the representative and compatible with base
change, and `Pic^C` is an fppf sheaf whose sections are those satisfying the condition at every
point. No hypothesis on `p : X ⟶ S` or on the test schemes is used. -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.RelativePicard Scheme.Modules.Invertible

universe u

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- The fppf covering sieves contain fppf morphisms through every point. -/
example {Y : Scheme.{u}} {R : Sieve Y} (hR : R ∈ Scheme.fppfTopology Y) (y : Y) :
    ∃ (V : Scheme.{u}) (h : V ⟶ Y), R h ∧ Flat h ∧ LocallyOfFinitePresentation h ∧
      y ∈ Set.range h :=
  Scheme.exists_flat_mem_range_of_mem_fppfTopology hR y

/-- The condition that always holds is a fiber condition. -/
example : FiberCondition p where
  Holds _ _ _ := True
  holds_map _ _ _ := Iff.rfl
  isOpen_setOf_holds _ _ _ := isOpen_univ

/-- A fiber condition from a condition on line bundles, here the condition that always holds. -/
example : FiberCondition p :=
  FiberCondition.ofLineBundle (fun _ _ _ ↦ True) (fun _ _ _ _ _ ↦ Iff.rfl)
    (fun _ _ _ ↦ Iff.rfl) (fun _ _ _ ↦ isOpen_univ)

variable (C : FiberCondition p)

example {T : Over S} (a : (familyPicardFunctor p).obj (op T)) (t : T.left)
    (s : Spec (T.left.residueField t)) :
    C.Holds T a t ↔
      C.Holds _ ((familyPicardFunctor p).map (FiberCondition.residuePoint T t).op a) s :=
  C.holds_iff_holds_residuePoint a t s

example {T : Over S} (a : (familyPicardFunctor p).obj (op T))
    (c : (basePicardFunctor S).obj (op T)) (t : T.left) :
    C.Holds T (a + (basePullback p).app (op T) c) t ↔ C.Holds T a t :=
  C.holds_add_basePullback_iff a c t

example {W : Over S} {a b : (familyPicardFunctor p).obj (op W)}
    (h : (quotientProjection p ≫ toFppfPicardSheaf p).app (op W) a =
      (quotientProjection p ≫ toFppfPicardSheaf p).app (op W) b) (w : W.left) :
    C.Holds W a w ↔ C.Holds W b w :=
  C.holds_iff_of_eq h w

example {T V : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) (h : V ⟶ T)
    (a : (familyPicardFunctor p).obj (op V))
    (ha : (quotientProjection p ≫ toFppfPicardSheaf p).app (op V) a =
      (fppfPicardSheaf p).obj.map h.op ξ) (v : V.left) :
    C.HoldsAt ξ (h.left v) ↔ C.Holds V a v :=
  C.holdsAt_iff ξ h a ha v

example {T T' : Over S} (g : T' ⟶ T) (ξ : (fppfPicardSheaf p).obj.obj (op T)) (t' : T'.left) :
    C.HoldsAt ((fppfPicardSheaf p).obj.map g.op ξ) t' ↔ C.HoldsAt ξ (g.left t') :=
  C.holdsAt_map g ξ t'

example : Presieve.IsSheaf (Scheme.fppfTopology.over S) C.subfunctor.toFunctor :=
  C.isSheaf_subfunctor

example {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    ξ ∈ C.subfunctor.obj (op T) ↔ ∀ t : T.left, C.HoldsAt ξ t :=
  C.mem_subfunctor_iff ξ

example {T : Over S} (a : (familyPicardFunctor p).obj (op T)) :
    (quotientProjection p ≫ toFppfPicardSheaf p).app (op T) a ∈ C.subfunctor.obj (op T) ↔
      ∀ t : T.left, C.Holds T a t :=
  C.app_mem_subfunctor_iff a

example {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) (t : T.left) :
    ∃ (V : Scheme.{u}) (h : V ⟶ T.left)
      (a : (familyPicardFunctor p).obj (op (Over.mk (h ≫ T.hom)))),
      Flat h ∧ LocallyOfFinitePresentation h ∧ t ∈ Set.range h ∧
        (quotientProjection p ≫ toFppfPicardSheaf p).app _ a =
          (fppfPicardSheaf p).obj.map (Over.homMk h : Over.mk (h ≫ T.hom) ⟶ T).op ξ :=
  FiberCondition.exists_flat_app_eq ξ t

/-- The conjunction of two fiber conditions cuts out the intersection of their subsheaves. -/
example (D : FiberCondition p) : (C ⊓ D).subfunctor = C.subfunctor ⊓ D.subfunctor :=
  C.subfunctor_inf D

example (D : FiberCondition p) {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T))
    (t : T.left) : (C ⊓ D).HoldsAt ξ t ↔ C.HoldsAt ξ t ∧ D.HoldsAt ξ t :=
  C.inf_holdsAt D ξ t

/-- The image presheaf is contained in the subsheaf. -/
example : C.imageSubfunctor ≤ C.subfunctor :=
  C.imageSubfunctor.le_sheafify _

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.mem_subfunctor_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FiberCondition.mem_subfunctor_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.holdsAt_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FiberCondition.holdsAt_iff
