/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.BaseChangeSource
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The original finite cover of the projective line after ring base change

The map is the literal Over pullback of the supplied cover followed by the
inverse of the existing native projective-line base-change comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (σ : R →+* S) {Y : Scheme.{u}} (p : Y ⟶ Scheme.ProjectiveLine.projectiveP1 R)

/-- The actual Over pullback map followed by the original line isomorphism. -/
def finiteCoverBaseChangeOverMap :
    Over.mk (pullback.snd (p ≫ Scheme.ProjectiveLine.structureMap R)
      (Spec.map (CommRingCat.ofHom σ))) ⟶
        Over.mk (Scheme.ProjectiveLine.structureMap S) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom σ))).map
      (Over.homMk p rfl : Over.mk (p ≫ Scheme.ProjectiveLine.structureMap R) ⟶
        Over.mk (Scheme.ProjectiveLine.structureMap R)) ≫
    (BinaryFormProduct.lineOverBaseChangeIso σ).inv

/-- The original underlying map on the literal chosen coefficient pullback. -/
def finiteCoverBaseChangeMap :
    pullback (p ≫ Scheme.ProjectiveLine.structureMap R)
      (Spec.map (CommRingCat.ofHom σ)) ⟶ Scheme.ProjectiveLine.projectiveP1 S :=
  (finiteCoverBaseChangeOverMap σ p).left

@[reassoc (attr := simp)]
theorem finiteCoverBaseChangeMap_structureMap :
    finiteCoverBaseChangeMap σ p ≫ Scheme.ProjectiveLine.structureMap S =
      pullback.snd (p ≫ Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) :=
  (finiteCoverBaseChangeOverMap σ p).w

instance [IsFinite p] : IsFinite (finiteCoverBaseChangeMap σ p) := by
  let a : Over.mk (p ≫ Scheme.ProjectiveLine.structureMap R) ⟶
      Over.mk (Scheme.ProjectiveLine.structureMap R) := Over.homMk p rfl
  let ha : IsFinite (((Over.pullback (Spec.map (CommRingCat.ofHom σ))).map a).left) :=
    MorphismProperty.overPullbackMap (P := @IsFinite)
      (Spec.map (CommRingCat.ofHom σ)) a (by change IsFinite p; infer_instance)
  let e := BinaryFormProduct.lineOverBaseChangeIso σ
  let : IsIso e.inv.left := inferInstanceAs
    (IsIso ((Over.forget (Spec (.of S))).map e.inv))
  change IsFinite (((Over.pullback (Spec.map (CommRingCat.ofHom σ))).map a).left ≫ e.inv.left)
  exact MorphismProperty.comp_mem (@IsFinite) _ _ ha inferInstance

end AlgebraicGeometry.ProjectiveSpace
