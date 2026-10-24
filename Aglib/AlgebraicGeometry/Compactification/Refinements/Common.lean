/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Uniqueness
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Actual common refinements of dense compactifications

The common refinement is the native schematic image of the pair of original
open immersions into the native fibre product. Quasi-compactness of the original
morphism suffices; no new compactification existence theorem is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]

instance quasiCompact_j (C : DenseCompactification f) : QuasiCompact C.j := by
  have : QuasiCompact (C.j ≫ C.p) := by rw [C.fac]; infer_instance
  exact QuasiCompact.of_comp C.j C.p

/-- The pair of the original open immersions into the actual fibre product. -/
def pair (C D : DenseCompactification f) : X ⟶ pullback C.p D.p :=
  pullback.lift C.j D.j (C.fac.trans D.fac.symm)

omit [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma pair_fst (C D : DenseCompactification f) :
    pair C D ≫ pullback.fst C.p D.p = C.j := by
  exact pullback.lift_fst _ _ _

omit [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma pair_snd (C D : DenseCompactification f) :
    pair C D ≫ pullback.snd C.p D.p = D.j := by
  exact pullback.lift_snd _ _ _

instance pair_isImmersion (C D : DenseCompactification f) :
    IsImmersion (pair C D) := by
  have : IsImmersion (pair C D ≫ pullback.fst C.p D.p) := by
    rw [pair_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst C.p D.p)

instance pair_quasiCompact (C D : DenseCompactification f) :
    QuasiCompact (pair C D) := by
  have : QuasiCompact (pair C D ≫ pullback.fst C.p D.p) := by
    rw [pair_fst]
    infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst C.p D.p)

/-- The common refinement is the native scheme-theoretic image of the pair. -/
def common (C D : DenseCompactification f) : DenseCompactification f where
  toCompactification := Compactification.ofImmersion f (pair C D)
    (pullback.fst C.p D.p ≫ C.p) (by simp)
  isSchemeTheoreticallyDominant_j := inferInstance

/-- The first proper projection from the actual common refinement. -/
def commonToLeft (C D : DenseCompactification f) : common C D ⟶ C where
  hom := (pair C D).imageι ≫ pullback.fst C.p D.p
  isProper_hom :=
    inferInstanceAs (IsProper ((pair C D).imageι ≫ pullback.fst C.p D.p))
  open_fac := by
    change (pair C D).toImage ≫ ((pair C D).imageι ≫ pullback.fst C.p D.p) = C.j
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, pair_fst]
  base_fac := Category.assoc _ _ _

/-- The second proper projection from the actual common refinement. -/
def commonToRight (C D : DenseCompactification f) : common C D ⟶ D where
  hom := (pair C D).imageι ≫ pullback.snd C.p D.p
  isProper_hom :=
    inferInstanceAs (IsProper ((pair C D).imageι ≫ pullback.snd C.p D.p))
  open_fac := by
    change (pair C D).toImage ≫ ((pair C D).imageι ≫ pullback.snd C.p D.p) = D.j
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, pair_snd]
  base_fac := by
    change ((pair C D).imageι ≫ pullback.snd C.p D.p) ≫ D.p =
      (pair C D).imageι ≫ (pullback.fst C.p D.p ≫ C.p)
    rw [Category.assoc, pullback.condition]

@[simp]
lemma commonToLeft_hom (C D : DenseCompactification f) :
    (commonToLeft C D).hom = (pair C D).imageι ≫ pullback.fst C.p D.p := rfl

@[simp]
lemma commonToRight_hom (C D : DenseCompactification f) :
    (commonToRight C D).hom = (pair C D).imageι ≫ pullback.snd C.p D.p := rfl

/-- Actual common refinements and schematic-density uniqueness give all finite
cone conditions apart from nonemptiness. -/
instance : IsCofilteredOrEmpty (DenseCompactification f) where
  cone_objs C D := ⟨common C D, commonToLeft C D, commonToRight C D, trivial⟩
  cone_maps C _ _ _ := ⟨C, 𝟙 C, Subsingleton.elim _ _⟩

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
