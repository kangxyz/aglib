/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Original closed singular fibres under flat preimmersion base change

The same actual pullback square identifies the closed singular points over
an original closed image point. The forward map is the original projection.
Global closedness of its image is proved on the entire original closed fibre,
not inferred from closedness inside an arbitrary open chart.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {P Z Y X : Scheme.{u}} {c : P ⟶ Z} {d : P ⟶ Y}
    {f : Z ⟶ X} {j : Y ⟶ X} (H : IsPullback c d f j)

include H

/-- Over a closed image point, the original preimmersion projection sends a
closed source point to a globally closed target point. -/
theorem isClosed_singleton_image_of_isPullback_of_preimmersion
    [IsPreimmersion j] (x : Y) (hx : IsClosed ({j x} : Set X))
    (z : P) (hz : d z = x) (hclosed : IsClosed ({z} : Set P)) :
    IsClosed ({c z} : Set Z) := by
  let : IsPreimmersion c :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip inferInstance
  let F : Set Z := f ⁻¹' ({j x} : Set X)
  have hF : c '' (d ⁻¹' ({x} : Set Y)) = F := by
    simpa only [F, Set.image_singleton] using
      (image_preimage_eq_of_isPullback H.flip ({x} : Set Y))
  have hFrange : F ⊆ Set.range c := by
    rw [← hF]
    exact Set.image_subset_range _ _
  have hcz : c z ∈ F := by
    have h := congrArg (fun g : P ⟶ X => g z) H.w
    change f (c z) = j (d z) at h
    exact h.trans (congrArg j hz)
  obtain ⟨C, hC, himage⟩ :=
    c.isEmbedding.isInducing.image_eq_isClosed_inter_range hclosed
  rw [Set.image_singleton] at himage
  have hCz : c z ∈ C := by
    have h : c z ∈ ({c z} : Set Z) := Set.mem_singleton _
    rw [himage] at h
    exact h.1
  have hset : ({c z} : Set Z) = C ∩ F := by
    ext y
    constructor
    · rintro rfl
      exact ⟨hCz, hcz⟩
    · intro hy
      have h : y ∈ C ∩ Set.range c := ⟨hy.1, hFrange hy.2⟩
      rwa [← himage] at h
  rw [hset]
  exact hC.inter (hx.preimage f.continuous)

/-- The actual projection preserves and reflects global closedness over the
specified closed image root. -/
theorem isClosed_singleton_iff_of_isPullback_of_preimmersion
    [IsPreimmersion j] (x : Y) (hx : IsClosed ({j x} : Set X))
    (z : P) (hz : d z = x) :
    IsClosed ({z} : Set P) ↔ IsClosed ({c z} : Set Z) := by
  refine ⟨isClosed_singleton_image_of_isPullback_of_preimmersion H x hx z hz, ?_⟩
  intro h
  let : IsPreimmersion c :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip inferInstance
  have he : c ⁻¹' ({c z} : Set Z) = {z} := by
    ext a
    exact c.isEmbedding.injective.eq_iff
  rw [← he]
  exact h.preimage c.continuous

private theorem nonregular_iff_of_isPullback_of_flat_of_preimmersion
    [Flat j] [IsPreimmersion j] (z : P) :
    (¬ IsRegularLocalRing (P.presheaf.stalk z)) ↔
      ¬ IsRegularLocalRing (Z.presheaf.stalk (c z)) := by
  let : Flat c := MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  let : IsPreimmersion c :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip inferInstance
  let : IsIso (c.stalkMap z) := Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks c z
  let e := (asIso (c.stalkMap z)).commRingCatIsoToRingEquiv
  constructor
  · intro hs hr
    let : IsRegularLocalRing (Z.presheaf.stalk (c z)) := hr
    exact hs (IsRegularLocalRing.of_ringEquiv e)
  · intro hs hr
    let : IsRegularLocalRing (P.presheaf.stalk z) := hr
    exact hs (IsRegularLocalRing.of_ringEquiv e.symm)

/-- The original projection induces an equivalence on actual globally closed
singular points in the specified fibre. Its stalk comparison is the original
flat preimmersion stalk map, not an assumed replacement local ring. -/
def closedSingularFiberEquivOfIsPullback
    [Flat j] [IsPreimmersion j] (x : Y) (hx : IsClosed ({j x} : Set X)) :
    {z : P // d z = x ∧ IsClosed ({z} : Set P) ∧
      ¬ IsRegularLocalRing (P.presheaf.stalk z)} ≃
    {y : Z // f y = j x ∧ IsClosed ({y} : Set Z) ∧
      ¬ IsRegularLocalRing (Z.presheaf.stalk y)} :=
  Equiv.ofBijective
    (fun z => ⟨c z.val, by
      refine ⟨?_, isClosed_singleton_image_of_isPullback_of_preimmersion
        H x hx z.val z.property.1 z.property.2.1, ?_⟩
      · have h := congrArg (fun g : P ⟶ X => g z.val) H.w
        change f (c z.val) = j (d z.val) at h
        exact h.trans (congrArg j z.property.1)
      · exact (nonregular_iff_of_isPullback_of_flat_of_preimmersion H z.val).mp
          z.property.2.2⟩)
    (by
      let : IsPreimmersion c :=
        MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip inferInstance
      constructor
      · intro a b hab
        apply Subtype.ext
        apply c.isEmbedding.injective
        exact congrArg (fun y : {y : Z // f y = j x ∧ IsClosed ({y} : Set Z) ∧
          ¬ IsRegularLocalRing (Z.presheaf.stalk y)} => y.val) hab
      · intro y
        obtain ⟨z, hcz, hdz⟩ := exists_preimage_of_isPullback H y.val x y.property.1
        have hc : IsClosed ({c z} : Set Z) := by
          simpa only [hcz] using y.property.2.1
        have hs : ¬ IsRegularLocalRing (Z.presheaf.stalk (c z)) :=
          Eq.mpr (congrArg (fun q : Z => ¬ IsRegularLocalRing (Z.presheaf.stalk q)) hcz)
            y.property.2.2
        refine ⟨⟨z, hdz,
          (isClosed_singleton_iff_of_isPullback_of_preimmersion H x hx z hdz).mpr hc,
          (nonregular_iff_of_isPullback_of_flat_of_preimmersion H z).mpr hs⟩, ?_⟩
        exact Subtype.ext hcz)

@[simp] theorem closedSingularFiberEquivOfIsPullback_apply_val
    [Flat j] [IsPreimmersion j] (x : Y) (hx : IsClosed ({j x} : Set X))
    (z : {z : P // d z = x ∧ IsClosed ({z} : Set P) ∧
      ¬ IsRegularLocalRing (P.presheaf.stalk z)}) :
    (closedSingularFiberEquivOfIsPullback H x hx z).val = c z.val := rfl

/-- The inverse equivalence lifts to the same actual target point. -/
theorem closedSingularFiberEquivOfIsPullback_symm_fst
    [Flat j] [IsPreimmersion j] (x : Y) (hx : IsClosed ({j x} : Set X))
    (y : {y : Z // f y = j x ∧ IsClosed ({y} : Set Z) ∧
      ¬ IsRegularLocalRing (Z.presheaf.stalk y)}) :
    c ((closedSingularFiberEquivOfIsPullback H x hx).symm y).val = y.val := by
  exact congrArg (fun y : {y : Z // f y = j x ∧ IsClosed ({y} : Set Z) ∧
    ¬ IsRegularLocalRing (Z.presheaf.stalk y)} => y.val)
    ((closedSingularFiberEquivOfIsPullback H x hx).apply_symm_apply y)

/-- The other projection of the actual inverse point is the original root. -/
theorem closedSingularFiberEquivOfIsPullback_symm_snd
    [Flat j] [IsPreimmersion j] (x : Y) (hx : IsClosed ({j x} : Set X))
    (y : {y : Z // f y = j x ∧ IsClosed ({y} : Set Z) ∧
      ¬ IsRegularLocalRing (Z.presheaf.stalk y)}) :
    d ((closedSingularFiberEquivOfIsPullback H x hx).symm y).val = x :=
  ((closedSingularFiberEquivOfIsPullback H x hx).symm y).property.1

end AlgebraicGeometry.Scheme
