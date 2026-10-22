/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.At
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Locus
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Target neighborhoods of etale stalk base changes

For a closed scheme morphism, the image of the complement of its source
etale locus is closed. Removing it gives the largest target open over which
the morphism is etale. In particular, a finitely presented finite morphism
whose actual target-stalk base change is etale is etale over a neighborhood
of that target point. No flatness of the original morphism is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u
variable {Z X : Scheme.{u}} (f : Z ⟶ X)

/-- The points admitting an etale source neighborhood form an open set. -/
theorem isOpen_etaleAt : IsOpen {z : Z | f.etaleAt z} := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨U, hz, hU⟩
  exact ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hz⟩

/-- The actual source etale locus, defined by its open-neighborhood property. -/
def etaleSourceOpen : Z.Opens := ⟨{z | f.etaleAt z}, f.isOpen_etaleAt⟩

/-- Source-neighborhood etaleness pulls back along an open immersion. -/
theorem etaleAt.comp_openImmersion {W : Scheme.{u}} (i : W ⟶ Z)
    [IsOpenImmersion i] (w : W) (h : f.etaleAt (i w)) :
    (i ≫ f).etaleAt w := by
  obtain ⟨U, hw, hU⟩ := h
  let : Etale (U.ι ≫ f) := hU
  refine ⟨i ⁻¹ᵁ U, hw, ?_⟩
  have heq : (i ⁻¹ᵁ U).ι ≫ (i ≫ f) = (i ∣_ U) ≫ (U.ι ≫ f) := by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rw [heq]
  infer_instance

/-- Any target open whose entire preimage is in the source etale locus is
an etale target neighborhood. -/
theorem etale_restrict_of_preimage_le_etaleSourceOpen (U : X.Opens)
    (hU : f ⁻¹ᵁ U ≤ f.etaleSourceOpen) : Etale (f ∣_ U) := by
  have : Etale ((f ⁻¹ᵁ U).ι ≫ f) :=
    etale_of_forall_etaleAt _ fun z =>
      etaleAt.comp_openImmersion f (f ⁻¹ᵁ U).ι z (hU z.property)
  have : Etale ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  exact Etale.of_comp (f ∣_ U) U.ι

/-- For a closed morphism, remove the image of every non-etale source point. -/
def etaleTargetOpen (hf : IsClosedMap f) : X.Opens :=
  ⟨(f '' (f.etaleSourceOpen : Set Z)ᶜ)ᶜ,
    (hf _ f.etaleSourceOpen.isOpen.isClosed_compl).isOpen_compl⟩

/-- The full inverse image of the target etale open is contained in the
source etale locus, including every point of every retained fibre. -/
theorem preimage_etaleTargetOpen_le (hf : IsClosedMap f) :
    f ⁻¹ᵁ f.etaleTargetOpen hf ≤ f.etaleSourceOpen := by
  intro z hz
  by_contra h
  exact hz ⟨z, h, rfl⟩

/-- The original morphism is etale on the target open produced by closedness. -/
theorem etale_restrict_etaleTargetOpen (hf : IsClosedMap f) :
    Etale (f ∣_ f.etaleTargetOpen hf) :=
  f.etale_restrict_of_preimage_le_etaleSourceOpen _ (f.preimage_etaleTargetOpen_le hf)

/-- Etaleness after the actual target-stalk base change gives a target
neighborhood for a closed, locally finitely presented morphism. -/
theorem exists_etale_target_neighborhood_of_etale_stalkBaseChange
    [LocallyOfFinitePresentation f] (hf : IsClosedMap f) (x : X)
    (hx : Etale (pullback.snd f (X.fromSpecStalk x))) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (f ∣_ U) := by
  refine ⟨f.etaleTargetOpen hf, ?_, f.etale_restrict_etaleTargetOpen hf⟩
  rintro ⟨z, hz, hzx⟩
  apply hz
  exact LocalRing.Etale.exists_etale_neighborhood_of_etale_stalkBaseChange f z
    (by
      change f z = x at hzx
      subst x
      exact hx)

/-- The finite-morphism version of the target-stalk neighborhood criterion.
Finite presentation is explicit so that arbitrary non-Noetherian targets
are not silently assumed to satisfy it. -/
theorem exists_etale_target_neighborhood_of_finite
    [IsFinite f] [LocallyOfFinitePresentation f] (x : X)
    (hx : Etale (pullback.snd f (X.fromSpecStalk x))) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (f ∣_ U) :=
  f.exists_etale_target_neighborhood_of_etale_stalkBaseChange f.isClosedMap x hx

/-- The finite target-stalk criterion can be refined to an affine open
neighborhood inside any prescribed target neighborhood. -/
theorem exists_affine_etale_target_neighborhood_of_finite
    [IsFinite f] [LocallyOfFinitePresentation f] (x : X)
    (hx : Etale (pullback.snd f (X.fromSpecStalk x)))
    (V : X.Opens) (hxV : x ∈ V) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V ∧ Etale (f ∣_ U) := by
  obtain ⟨W, hxW, hW⟩ := f.exists_etale_target_neighborhood_of_finite x hx
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ W ⊓ V from ⟨hxW, hxV⟩)
  refine ⟨U, hU, hxU, hUW.trans inf_le_right, ?_⟩
  have hpre : f ⁻¹ᵁ W ≤ f.etaleSourceOpen := by
    intro z hz
    let : Etale (f ∣_ W) := hW
    have : Etale ((f ⁻¹ᵁ W).ι ≫ f) := by
      rw [← morphismRestrict_ι]
      infer_instance
    exact ⟨f ⁻¹ᵁ W, hz, inferInstance⟩
  exact f.etale_restrict_of_preimage_le_etaleSourceOpen U
    ((f.preimage_mono (hUW.trans inf_le_left)).trans hpre)

end AlgebraicGeometry.Scheme.Hom
