/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Reindex
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Actual base change of the native universe-polymorphic projective line

Native coordinate reindexing transports the existing projective-space
Cartesian square, preserving the existing projective-line structure map.
An original affine morphism over the line then gives an actual affine
morphism from its literal coefficient base change to the new native line.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original literal-to-lifted coordinate comparison respects the existing
native projective-line structure map in the inverse direction. -/
theorem finUliftIso_inv_projectiveLine_structure (R : Type u) [CommRing R] :
    (ProjectiveSpace.finUliftIso R 2).inv ≫ Scheme.ProjectiveLine.structureMap R =
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) := by
  change (ProjectiveSpace.finUliftIso R 2).inv ≫
    ProjectiveSpace.polynomialToSpec R (Fin 2) = _
  rw [← ProjectiveSpace.finUliftIso_hom_toSpec]
  simp

/-- The actual native projective-line coefficient morphism, through the
existing literal/lifted coordinate isomorphisms. -/
def projectiveLineBaseMap (σ : R →+* S) :
    Scheme.ProjectiveLine.projectiveP1 S ⟶ Scheme.ProjectiveLine.projectiveP1 R :=
  (ProjectiveSpace.finUliftIso S 2).hom ≫
    ProjectiveSpace.map σ (ULift.{u} (Fin 2)) ≫ (ProjectiveSpace.finUliftIso R 2).inv

/-- The existing native projective line commutes with the original coefficient
base change, in arbitrary coefficient universes. -/
theorem projectiveLineBaseMap_isPullback (σ : R →+* S) :
    IsPullback (projectiveLineBaseMap σ) (Scheme.ProjectiveLine.structureMap S)
      (Scheme.ProjectiveLine.structureMap R) (Spec.map (CommRingCat.ofHom σ)) := by
  refine (ProjectiveSpace.isPullback_map σ (ULift.{u} (Fin 2))).of_iso
    (ProjectiveSpace.finUliftIso S 2).symm (ProjectiveSpace.finUliftIso R 2).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [projectiveLineBaseMap]
  · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id] using
      (finUliftIso_inv_projectiveLine_structure S).symm
  · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id] using
      (finUliftIso_inv_projectiveLine_structure R).symm
  · simp

/-- The canonical comparison with the actual native projective-line pullback. -/
def projectiveLineBaseChangeIso (σ : R →+* S) :
    Scheme.ProjectiveLine.projectiveP1 S ≅
      Limits.pullback (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) :=
  (projectiveLineBaseMap_isPullback σ).isoPullback

@[reassoc (attr := simp)]
theorem projectiveLineBaseChangeIso_hom_fst (σ : R →+* S) :
    (projectiveLineBaseChangeIso σ).hom ≫
      Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) = projectiveLineBaseMap σ :=
  (projectiveLineBaseMap_isPullback σ).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem projectiveLineBaseChangeIso_hom_snd (σ : R →+* S) :
    (projectiveLineBaseChangeIso σ).hom ≫
      Limits.pullback.snd (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) = Scheme.ProjectiveLine.structureMap S :=
  (projectiveLineBaseMap_isPullback σ).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem projectiveLineBaseChangeIso_inv_structure (σ : R →+* S) :
    (projectiveLineBaseChangeIso σ).inv ≫ Scheme.ProjectiveLine.structureMap S =
      Limits.pullback.snd (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) := by
  apply (cancel_epi (projectiveLineBaseChangeIso σ).hom).mp
  simp

variable {X : Scheme.{u}} (σ : R →+* S)
  (p : X ⟶ Scheme.ProjectiveLine.projectiveP1 R)
  (f : X ⟶ Spec (CommRingCat.of R))
  (h : p ≫ Scheme.ProjectiveLine.structureMap R = f)

/-- The actual coefficient base change maps to the actual projective-line
pullback, preserving both original projections. -/
def projectiveLineBaseChangeLift :
    Limits.pullback (Spec.map (CommRingCat.ofHom σ)) f ⟶
      Limits.pullback (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) :=
  Limits.pullback.lift
    (Limits.pullback.snd (Spec.map (CommRingCat.ofHom σ)) f ≫ p)
    (Limits.pullback.fst (Spec.map (CommRingCat.ofHom σ)) f)
    (by rw [Category.assoc, h]; exact Limits.pullback.condition.symm)

@[reassoc (attr := simp)]
theorem projectiveLineBaseChangeLift_fst :
    projectiveLineBaseChangeLift σ p f h ≫
      Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) =
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom σ)) f ≫ p :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem projectiveLineBaseChangeLift_snd :
    projectiveLineBaseChangeLift σ p f h ≫
      Limits.pullback.snd (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ)) =
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom σ)) f :=
  Limits.pullback.lift_snd _ _ _

/-- The comparison is the actual base change of the original morphism to
the projective line. -/
theorem projectiveLineBaseChangeLift_isPullback :
    IsPullback (Limits.pullback.snd (Spec.map (CommRingCat.ofHom σ)) f)
      (projectiveLineBaseChangeLift σ p f h) p
      (Limits.pullback.fst (Scheme.ProjectiveLine.structureMap R)
        (Spec.map (CommRingCat.ofHom σ))) := by
  apply IsPullback.of_bot _ (projectiveLineBaseChangeLift_fst σ p f h).symm
    (IsPullback.of_hasPullback (Scheme.ProjectiveLine.structureMap R)
      (Spec.map (CommRingCat.ofHom σ)))
  rw [projectiveLineBaseChangeLift_snd, h]
  exact (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom σ)) f).flip

/-- The actual base-changed morphism to the existing native projective line. -/
def projectiveLineBaseChangeArrow :
    Limits.pullback (Spec.map (CommRingCat.ofHom σ)) f ⟶
      Scheme.ProjectiveLine.projectiveP1 S :=
  projectiveLineBaseChangeLift σ p f h ≫ (projectiveLineBaseChangeIso σ).inv

/-- The original affine morphism stays affine on this actual base change. -/
instance projectiveLineBaseChangeArrow_isAffineHom [IsAffineHom p] :
    IsAffineHom (projectiveLineBaseChangeArrow σ p f h) := by
  have : IsAffineHom (projectiveLineBaseChangeLift σ p f h) :=
    MorphismProperty.of_isPullback (projectiveLineBaseChangeLift_isPullback σ p f h)
      inferInstance
  dsimp only [projectiveLineBaseChangeArrow]
  infer_instance

/-- The actual base-changed map retains the original structure-map equation. -/
@[reassoc (attr := simp)]
theorem projectiveLineBaseChangeArrow_structure :
    projectiveLineBaseChangeArrow σ p f h ≫ Scheme.ProjectiveLine.structureMap S =
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom σ)) f := by
  simp [projectiveLineBaseChangeArrow]

end AlgebraicGeometry.Scheme.Modules.Invertible
