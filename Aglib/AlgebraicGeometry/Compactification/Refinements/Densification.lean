/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Uniqueness

/-!
# Densification by the original scheme-theoretic image

An arbitrary compactification with quasi-compact open source has a canonical
schematically dense refinement. The comparison is the original closed image
inclusion. Compatible ambient maps lift through these images by the existing
closed-target factorization theorem, not by an image/base-change assumption.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.Compactification

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Replace the ambient scheme by the native image of the original open source. -/
def densify (C : Compactification f) [QuasiCompact C.j] : DenseCompactification f where
  toCompactification := ofImmersion f C.j C.p C.fac
  isSchemeTheoreticallyDominant_j := inferInstance

/-- The comparison to the original compactification is its closed image inclusion. -/
def densifyι (C : Compactification f) [QuasiCompact C.j] :
    (densify C).Xbar ⟶ C.Xbar := C.j.imageι

instance densifyι_isClosedImmersion (C : Compactification f) [QuasiCompact C.j] :
    IsClosedImmersion (densifyι C) :=
  inferInstanceAs (IsClosedImmersion C.j.imageι)

@[reassoc (attr := simp)]
lemma densify_j_ι (C : Compactification f) [QuasiCompact C.j] :
    (densify C).j ≫ densifyι C = C.j := C.j.toImage_imageι

@[reassoc (attr := simp)]
lemma densifyι_p (C : Compactification f) [QuasiCompact C.j] :
    densifyι C ≫ C.p = (densify C).p := rfl

/-- The closed densification map is Cartesian over the original open source,
without a density assumption on the original ambient scheme. -/
lemma isPullback_densify (C : Compactification f) [QuasiCompact C.j] :
    IsPullback (densify C).j (𝟙 X) (densifyι C) C.j :=
  (IsPullback.of_horiz_isIso_mono
    (show CommSq (𝟙 X) (densify C).j C.j (densifyι C) from ⟨by simp⟩)).flip

variable (C D : Compactification f) [QuasiCompact C.j] [QuasiCompact D.j]
  (h : C.Xbar ⟶ D.Xbar) (ho : C.j ≫ h = D.j)

/-- Lift a compatible ambient map through the two original schematic images. -/
def densifyMap : C.j.image ⟶ D.j.image := by
  letI : IsSchemeTheoreticallyDominant C.j.toImage :=
    Scheme.isSchemeTheoreticallyDominant_toImage C.j
  exact Scheme.QuasiDomination.closedTargetLift C.j.toImage D.j.imageι
    (C.j.imageι ≫ h) D.j.toImage (by
      rw [← Category.assoc, C.j.toImage_imageι, D.j.toImage_imageι]
      exact ho)

omit [QuasiCompact D.j] in
/-- The image lift retains the original ambient map after the closed inclusion. -/
@[reassoc (attr := simp)]
lemma densifyMap_ι : densifyMap C D h ho ≫ D.j.imageι = C.j.imageι ≫ h := by
  let : IsSchemeTheoreticallyDominant C.j.toImage :=
    Scheme.isSchemeTheoreticallyDominant_toImage C.j
  exact Scheme.QuasiDomination.closedTargetLift_comp _ _ _ _ _

omit [QuasiCompact D.j] in
/-- The image lift retains the original open-source map. -/
@[reassoc (attr := simp)]
lemma densify_j_map : C.j.toImage ≫ densifyMap C D h ho = D.j.toImage := by
  let : IsSchemeTheoreticallyDominant C.j.toImage :=
    Scheme.isSchemeTheoreticallyDominant_toImage C.j
  exact Scheme.QuasiDomination.comp_closedTargetLift _ _ _ _ _

omit [QuasiCompact D.j] in
/-- The image lift retains the structural morphism when the ambient map does. -/
@[reassoc]
lemma densifyMap_p (hb : h ≫ D.p = C.p) :
    densifyMap C D h ho ≫ (D.j.imageι ≫ D.p) = C.j.imageι ≫ C.p := by
  rw [← Category.assoc, densifyMap_ι, Category.assoc, hb]

/-- A base-compatible ambient map yields an actual proper refinement after
schematic-image normalization. -/
def densifyRefinement (hb : h ≫ D.p = C.p) : densify C ⟶ densify D where
  hom := densifyMap C D h ho
  isProper_hom := by
    have : IsProper (densifyMap C D h ho ≫ (D.j.imageι ≫ D.p)) := by
      rw [densifyMap_p C D h ho hb]
      infer_instance
    exact IsProper.of_comp (densifyMap C D h ho) (D.j.imageι ≫ D.p)
  open_fac := densify_j_map C D h ho
  base_fac := densifyMap_p C D h ho hb

@[simp]
lemma densifyRefinement_hom (hb : h ≫ D.p = C.p) :
    (densifyRefinement C D h ho hb).hom = densifyMap C D h ho := rfl

end AlgebraicGeometry.Scheme.Hom.Compactification
