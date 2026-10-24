/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.IsomorphismLocus
public import Aglib.AlgebraicGeometry.Dimension.CodimensionTwo

/-!
# Actual restrictions of proper birational surface morphisms

The existing target isomorphism locus contains every normal target point
whose actual stalk has dimension at most one. Any actual open consisting
of such points therefore has an isomorphic original restriction.

For a local affine scheme of dimension at most two, every point other
than its closed point satisfies that stalk bound. This is stated without
defining a punctured spectrum or importing a cohomology owner.

The existing finite-complement theorem is reused. The additional pointwise
statement identifies the remaining stalk dimensions as exactly two.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

private theorem isIso_restrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V : Y.Opens) (hUV : U ≤ V) (hV : IsIso (f ∣_ V)) : IsIso (f ∣_ U) := by
  let W : V.toScheme.Opens := V.ι ⁻¹ᵁ U
  have hW : IsIso (f ∣_ V ∣_ W) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hV W
  have himage : V.ι ''ᵁ W = U := by
    change V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι,
      inf_eq_right.mpr hUV]
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V W ≪≫ morphismRestrictEq f himage)).mp hW

/-- The original proper birational map restricts to an isomorphism on every
actual target open whose actual stalks have dimension at most one. -/
theorem Hom.isIso_restrict_of_stalk_dimension_le_one
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (U : Y.Opens)
    (hdim : ∀ y ∈ U, ringKrullDim (Y.presheaf.stalk y) ≤ 1) : IsIso (f ∣_ U) := by
  apply isIso_restrict_of_le f U f.targetIsomorphismLocus
    _ f.isIso_restrict_targetIsomorphismLocus
  intro y hy
  have hcoheight : Order.coheight y ≤ 1 := by
    have h := hdim y hy
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_le_coe.mp h
  obtain ⟨V, hyV, hV⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_coheight_le_one f hff hY y hcoheight
  exact f.le_targetIsomorphismLocus V hV hyV

/-- Away from the closed point of a local affine scheme of dimension at most
two, the original target stalk has dimension at most one. -/
theorem ringKrullDim_stalk_le_one_of_ne_closedPoint
    (A : Type u) [CommRing A] [IsLocalRing A] (hdim : ringKrullDim A ≤ 2)
    (p : PrimeSpectrum A) (hp : p ≠ IsLocalRing.closedPoint A) :
    ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk p) ≤ 1 := by
  have htop : topologicalKrullDim (Spec (CommRingCat.of A)) ≤ 2 := by
    change topologicalKrullDim (PrimeSpectrum A) ≤ 2
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have hclosed : ¬ IsClosed ({p} : Set (Spec (CommRingCat.of A))) := by
    intro h
    apply hp
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp h)
  have h := coheight_le_one_of_not_isClosed_singleton_of_dimension_le_two
    (Spec (CommRingCat.of A)) htop p hclosed
  exact (ringKrullDim_stalk_eq_coheight (X := Spec (CommRingCat.of A)) p).le.trans
    (WithBot.coe_le_coe.mpr h)

/-- A point outside the actual target isomorphism locus has stalk dimension
exactly two when all original target stalks have dimension at most two. -/
theorem Hom.ringKrullDim_stalk_eq_two_of_not_mem_targetIsomorphismLocus
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdim : SurfaceDimensionAtMostTwo Y)
    (y : Y) (hy : y ∉ f.targetIsomorphismLocus) :
    ringKrullDim (Y.presheaf.stalk y) = 2 := by
  have hcoheight : Order.coheight y ≤ 2 := by
    have h := hdim y
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_le_coe.mp h
  have hnot : ¬ Order.coheight y ≤ 1 := by
    intro h
    obtain ⟨U, hyU, hU⟩ :=
      exists_isIso_restrict_of_isProper_birational_at_coheight_le_one f hff hY y h
    exact hy (f.le_targetIsomorphismLocus U hU hyU)
  have heq : Order.coheight y = 2 :=
    le_antisymm hcoheight (not_lt.mp fun h => hnot (ENat.lt_two_iff.mp h))
  rw [ringKrullDim_stalk_eq_coheight]
  exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) heq

end AlgebraicGeometry.Scheme
