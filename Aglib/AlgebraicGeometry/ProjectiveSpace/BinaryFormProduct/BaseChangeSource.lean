/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Basic
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts.BaseChange

/-!
# Arbitrary base change of the original binary-form product source

The original native projective line and the original native finite over-product
commute with every coefficient-ring map. The comparisons retain the original
pullback projections and the actual original base triangles.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

/-- Componentwise isomorphisms on the unchanged native finite over-product. -/
def finiteProductIso {B : Scheme.{u}} : {n : ℕ} →
    {X Y : Fin n → Over B} → (∀ i, X i ≅ Y i) →
      (Scheme.finiteProductOver X ≅ Scheme.finiteProductOver Y)
  | 0, _, _, _ => Iso.refl _
  | n + 1, _, _, e => prod.mapIso (e 0) (finiteProductIso (fun i : Fin n => e i.succ))

theorem finiteProductIso_hom_π {B : Scheme.{u}} {n : ℕ}
    {X Y : Fin n → Over B} (e : ∀ i, X i ≅ Y i) (i : Fin n) :
    (finiteProductIso e).hom ≫ Scheme.finiteProductOverπ Y i =
      Scheme.finiteProductOverπ X i ≫ (e i).hom := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      cases i using Fin.cases with
      | zero => simp [finiteProductIso, Scheme.finiteProductOverπ_zero]
      | succ i => simp [finiteProductIso, Scheme.finiteProductOverπ_succ, ih]

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The unchanged native projective line over the new ring is the actual
base change of the unchanged native projective line over the original ring. -/
def lineOverBaseChangeIso (σ : R →+* S) :
    Over.mk (Scheme.ProjectiveLine.structureMap S) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom σ))).obj
        (Over.mk (Scheme.ProjectiveLine.structureMap R)) := by
  let e : Over.mk (toSpec S (ULift.{u} (Fin 2))) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom σ))).obj
        (Over.mk (toSpec R (ULift.{u} (Fin 2)))) :=
    Over.isoMk (ProjectiveSpace.baseChangeIso σ (ULift.{u} (Fin 2)))
      (ProjectiveSpace.baseChangeIso_hom_snd σ (ULift.{u} (Fin 2)))
  exact finUliftOverIso S 2 ≪≫ e ≪≫
    ((Over.pullback (Spec.map (CommRingCat.ofHom σ))).mapIso (finUliftOverIso R 2)).symm

/-- The same original native over-product commutes with arbitrary original base change. -/
def sourceOverBaseChangeIso (σ : R →+* S) (n : ℕ) :
    product S n ≅ (Over.pullback (Spec.map (CommRingCat.ofHom σ))).obj (product R n) :=
  finiteProductIso (fun _i : Fin n => lineOverBaseChangeIso σ) ≪≫
    (Scheme.finiteProductOverPullbackIso (Spec.map (CommRingCat.ofHom σ)) (factor R n)).symm

/-- The actual scheme isomorphism with the original categorical pullback. -/
def sourceBaseChangeIso (σ : R →+* S) (n : ℕ) :
    source S n ≅ Limits.pullback (structureMap R n) (Spec.map (CommRingCat.ofHom σ)) :=
  (Over.forget _).mapIso (sourceOverBaseChangeIso σ n)

@[reassoc (attr := simp)]
theorem sourceBaseChangeIso_hom_snd (σ : R →+* S) (n : ℕ) :
    (sourceBaseChangeIso σ n).hom ≫
      Limits.pullback.snd (structureMap R n) (Spec.map (CommRingCat.ofHom σ)) =
        structureMap S n :=
  (sourceOverBaseChangeIso σ n).hom.w

/-- The original coefficient base-change map on the unchanged native source product. -/
def sourceBaseChangeMap (σ : R →+* S) (n : ℕ) : source S n ⟶ source R n :=
  (sourceBaseChangeIso σ n).hom ≫
    Limits.pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom σ))

/-- Original coefficient base change on an unchanged native projective-line factor. -/
def lineBaseChangeMap (σ : R →+* S) :
    Scheme.ProjectiveLine.projectiveP1 S ⟶ Scheme.ProjectiveLine.projectiveP1 R :=
  (finUliftIso S 2).hom ≫ ProjectiveSpace.map σ (ULift.{u} (Fin 2)) ≫ (finUliftIso R 2).inv

@[reassoc (attr := simp)]
theorem lineBaseChangeMap_lifted (σ : R →+* S) :
    lineBaseChangeMap σ ≫ (finUliftIso R 2).hom =
      (finUliftIso S 2).hom ≫ ProjectiveSpace.map σ (ULift.{u} (Fin 2)) := by
  simp only [lineBaseChangeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc (attr := simp)]
theorem lineBaseChangeMap_over (σ : R →+* S) :
    lineBaseChangeMap σ ≫ Scheme.ProjectiveLine.structureMap R =
      Scheme.ProjectiveLine.structureMap S ≫ Spec.map (CommRingCat.ofHom σ) := by
  have h : (finUliftIso R 2).inv ≫ Scheme.ProjectiveLine.structureMap R =
      toSpec R (ULift.{u} (Fin 2)) := (finUliftOverIso R 2).inv.w
  rw [lineBaseChangeMap, Category.assoc, Category.assoc, h, ProjectiveSpace.map_toSpec,
    ← Category.assoc, finUliftIso_hom_toSpec]
  rfl

theorem lineOverBaseChangeIso_hom_fst (σ : R →+* S) :
    (lineOverBaseChangeIso σ).hom.left ≫
      Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) = lineBaseChangeMap σ := by
  let t := (Over.pullback (Spec.map (CommRingCat.ofHom σ))).map (finUliftOverIso R 2).inv
  have ht : t.left ≫ Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
      (Spec.map (CommRingCat.ofHom σ)) =
        Limits.pullback.fst (toSpec R (ULift.{u} (Fin 2))) (Spec.map (CommRingCat.ofHom σ)) ≫
          (finUliftIso R 2).inv := by
    dsimp only [t, Over.pullback_map_left]
    exact Limits.pullback.lift_fst _ _ _
  change (finUliftIso S 2).hom ≫
    (ProjectiveSpace.baseChangeIso σ (ULift.{u} (Fin 2))).hom ≫ t.left ≫
      Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) = _
  rw [ht, ProjectiveSpace.baseChangeIso_hom_fst_assoc]
  rfl

/-- The source comparison preserves every original native factor projection. -/
theorem sourceOverBaseChangeIso_hom_π (σ : R →+* S) (n : ℕ) (i : Fin n) :
    (sourceOverBaseChangeIso σ n).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom σ))).map
        (Scheme.finiteProductOverπ (factor R n) i) =
      Scheme.finiteProductOverπ (factor S n) i ≫ (lineOverBaseChangeIso σ).hom := by
  dsimp only [sourceOverBaseChangeIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Scheme.finiteProductOverPullbackIso_inv_map_π]
  exact finiteProductIso_hom_π (fun _ : Fin n => lineOverBaseChangeIso σ) i

@[reassoc (attr := simp)]
theorem sourceBaseChangeMap_projection (σ : R →+* S) (n : ℕ) (i : Fin n) :
    sourceBaseChangeMap σ n ≫ projection R n i =
      projection S n i ≫ lineBaseChangeMap σ := by
  let t := (Over.pullback (Spec.map (CommRingCat.ofHom σ))).map
    (Scheme.finiteProductOverπ (factor R n) i)
  have ht : t.left ≫ Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
      (Spec.map (CommRingCat.ofHom σ)) =
        Limits.pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom σ)) ≫
          projection R n i := by
    dsimp only [t, Over.pullback_map_left]
    exact Limits.pullback.lift_fst _ _ _
  have h := congrArg (fun f => f.left ≫
    Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
      (Spec.map (CommRingCat.ofHom σ))) (sourceOverBaseChangeIso_hom_π σ n i)
  change (sourceOverBaseChangeIso σ n).hom.left ≫ t.left ≫
      Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) =
      projection S n i ≫ (lineOverBaseChangeIso σ).hom.left ≫
        Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
          (Spec.map (CommRingCat.ofHom σ)) at h
  rw [ht, lineOverBaseChangeIso_hom_fst] at h
  exact (Category.assoc _ _ _).trans h

-- The factor-projection and line comparison rules already supply simp normalization.
@[reassoc]
theorem sourceBaseChangeMap_liftedProjection (σ : R →+* S) (n : ℕ) (i : Fin n) :
    sourceBaseChangeMap σ n ≫ liftedProjection R n i =
      liftedProjection S n i ≫ ProjectiveSpace.map σ (ULift.{u} (Fin 2)) := by
  rw [← Category.assoc, sourceBaseChangeMap_projection, Category.assoc,
    lineBaseChangeMap_lifted]
  rfl

@[reassoc (attr := simp)]
theorem sourceBaseChangeMap_over (σ : R →+* S) (n : ℕ) :
    sourceBaseChangeMap σ n ≫ structureMap R n =
      structureMap S n ≫ Spec.map (CommRingCat.ofHom σ) := by
  rw [sourceBaseChangeMap, Category.assoc, Limits.pullback.condition,
    ← Category.assoc, sourceBaseChangeIso_hom_snd]

/-- The original source comparison is Cartesian, including the empty product. -/
theorem isPullback_sourceBaseChangeMap (σ : R →+* S) (n : ℕ) :
    IsPullback (sourceBaseChangeMap σ n) (structureMap S n)
      (structureMap R n) (Spec.map (CommRingCat.ofHom σ)) := by
  exact IsPullback.of_iso_pullback ⟨sourceBaseChangeMap_over σ n⟩
    (sourceBaseChangeIso σ n) rfl (sourceBaseChangeIso_hom_snd σ n)

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
