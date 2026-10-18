/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.FiniteBasePoint
public import Aglib.AlgebraicGeometry.FundamentalGroup.GeometricCoverModels

/-!
# CommonBaseStage

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite mk)

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

universe u
section Pair
variable {K : Type u} [Field K] {B : Scheme.{u}}
  (b : Spec (CommRingCat.of K) ⟶ B) (Z W : Scheme.FiniteEtale B)

/-- The fiber product of `Z` and `W` over `B` , regarded as a finite étale scheme over `B` . -/
def pairBaseCover : Scheme.FiniteEtale B := mk (pullback.fst Z.obj.hom W.obj.hom ≫ Z.obj.hom)

/-- The projection from the common fiber product cover to `Z` . -/
def pairBaseLeft : pairBaseCover Z W ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (pullback.fst Z.obj.hom W.obj.hom) rfl)

/-- The projection from the common fiber product cover to `W` . -/
def pairBaseRight : pairBaseCover Z W ⟶ W :=
  ObjectProperty.homMk (Over.homMk (pullback.snd Z.obj.hom W.obj.hom) pullback.condition.symm)

/-- The fiber point of the common cover whose projections are the supplied points `q` and `r`
. -/
def pairBasePoint (q : Fiber b Z) (r : Fiber b W) : Fiber b (pairBaseCover Z W) :=
  Over.homMk (pullback.lift q.left r.left ((Over.w q).trans (Over.w r).symm)) (by
    change pullback.lift q.left r.left _ ≫ (pullback.fst Z.obj.hom W.obj.hom ≫ Z.obj.hom) = b
    rw [pullback.lift_fst_assoc]
    exact Over.w q)

@[simp] theorem pairBasePoint_left (q : Fiber b Z) (r : Fiber b W) :
    (pairBasePoint b Z W q r).left ≫ pullback.fst Z.obj.hom W.obj.hom = q.left :=
  pullback.lift_fst _ _ _

@[simp] theorem pairBasePoint_right (q : Fiber b Z) (r : Fiber b W) :
    (pairBasePoint b Z W q r).left ≫ pullback.snd Z.obj.hom W.obj.hom = r.left :=
  pullback.lift_snd _ _ _
end Pair

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- A common finite separable field stage carrying two selected base points. -/
structure CommonFiniteSeparableBase (Z W : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) (r : Fiber (Spec.algebraMap K Ω) W) where
  /-- The finite subset of `Ω` indexing the common finite separable field stage. -/
  stage : Finset Ω
  /-- The morphism from the selected finite separable field cover to `Z` . -/
  left : SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω stage) ⟶ Z
  /-- The morphism from the selected finite separable field cover to `W` . -/
  right : SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω stage) ⟶ W
  left_point : (fiberToFinite (Spec.algebraMap K Ω)).map left (finiteSepPoint K Ω stage) = q
  right_point : (fiberToFinite (Spec.algebraMap K Ω)).map right (finiteSepPoint K Ω stage) = r

/-- Both points factor through one actual finite separable field cover. -/
def commonFiniteSeparableBase (Z W : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) (r : Fiber (Spec.algebraMap K Ω) W) :
    CommonFiniteSeparableBase K Ω Z W q r := by
  let P := pairBaseCover Z W
  let x := pairBasePoint (Spec.algebraMap K Ω) Z W q r
  let hs := FiniteBasePoint.exists_separable_field_point K Ω P x
  let s := hs.choose
  let xS := hs.choose_spec.choose
  have hxS := hs.choose_spec.choose_spec
  let a : SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω s) ⟶ P :=
    ObjectProperty.homMk xS
  refine ⟨s, a ≫ pairBaseLeft Z W, a ≫ pairBaseRight Z W, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom (FieldLimit.finiteField K Ω s).val.toRingHom) ≫
      Spec.algebraMap (finiteSepField K Ω s) (FieldLimit.finiteField K Ω s)) ≫
        (xS.left ≫ pullback.fst Z.obj.hom W.obj.hom) = q.left
    rw [← Category.assoc, hxS]
    exact pairBasePoint_left (Spec.algebraMap K Ω) Z W q r
  · apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom (FieldLimit.finiteField K Ω s).val.toRingHom) ≫
      Spec.algebraMap (finiteSepField K Ω s) (FieldLimit.finiteField K Ω s)) ≫
        (xS.left ≫ pullback.snd Z.obj.hom W.obj.hom) = r.left
    rw [← Category.assoc, hxS]
    exact pairBasePoint_right (Spec.algebraMap K Ω) Z W q r

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3b53b2c2573259e004c703665907d85592c645ad79768831b44ca4ff7447e1f1.
Definitions, hypotheses and universes are retained modulo native names. -/
