/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.BaseChangeSource
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Actual affine chart models of a pulled-back projective line

Every affine chart of the base of an original Cartesian P1 square has its
native projective-line model. The isomorphism is over that same affine
chart, retaining the actual first pullback projection.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

private theorem common_iso_projection {C : Type*} [Category* C]
    {A B P S : C} (eA : A ≅ P) (eB : B ≅ P)
    (a : A ⟶ S) (b : B ⟶ S) (p : P ⟶ S)
    (ha : eA.hom ≫ p = a) (hb : eB.hom ≫ p = b) :
    (eA ≪≫ eB.symm).hom ≫ b = a := by
  change (eA.hom ≫ eB.inv) ≫ b = a
  have hb' : eB.inv ≫ b = p := by
    rw [← hb, ← Category.assoc, eB.inv_hom_id, Category.id_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => eA.hom ≫ k) hb').trans ha)

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

open AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

private theorem isPullback_nativeLineMap
    {R T : Type u} [CommRing R] [CommRing T] (φ : R →+* T) :
    IsPullback (lineBaseChangeMap φ) (ProjectiveLine.structureMap T)
      (ProjectiveLine.structureMap R) (Spec.map (CommRingCat.ofHom φ)) := by
  let e := (Over.forget (Spec (.of T))).mapIso (lineOverBaseChangeIso φ)
  exact IsPullback.of_iso_pullback ⟨lineBaseChangeMap_over φ⟩ e
    (lineOverBaseChangeIso_hom_fst φ) (Over.w (lineOverBaseChangeIso φ).hom)

variable (R T : Type u) [CommRing R] [CommRing T]
  {X S : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ Spec (.of R))
  (g' : X ⟶ ProjectiveLine.projectiveP1 R)
  (H : IsPullback g' f (ProjectiveLine.structureMap R) g)
  (j : Spec (.of T) ⟶ S)

/-- The actual pullback to any original affine chart of a base-changed P1
is the native P1 of that chart, as an isomorphism over its spectrum. -/
def projectiveLineAffineChartIso :
    Over.mk (ProjectiveLine.structureMap T) ≅ Over.mk (pullback.fst j f) := by
  let φ : R →+* T := (Spec.preimage (j ≫ g)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = j ≫ g := by
    change Spec.map (Spec.preimage (j ≫ g)) = j ≫ g
    exact Spec.map_preimage (j ≫ g)
  have HL : IsPullback (lineBaseChangeMap φ) (ProjectiveLine.structureMap T)
      (ProjectiveLine.structureMap R) (j ≫ g) := by
    rw [← hφ]
    exact isPullback_nativeLineMap φ
  have HC : IsPullback (pullback.snd j f ≫ g') (pullback.fst j f)
      (ProjectiveLine.structureMap R) (j ≫ g) :=
    (IsPullback.of_hasPullback j f).flip.paste_horiz H
  exact Over.isoMk (HL.isoPullback ≪≫ HC.isoPullback.symm)
    (common_iso_projection HL.isoPullback HC.isoPullback
      (ProjectiveLine.structureMap T) (pullback.fst j f)
      (pullback.snd (ProjectiveLine.structureMap R) (j ≫ g))
      HL.isoPullback_hom_snd HC.isoPullback_hom_snd)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
