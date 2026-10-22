/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Open localization of the underlying schematic-image range

For a quasi-compact morphism, restriction of its schematic-image inclusion to
an open has underlying range equal to the closure of the restricted original
range. This is a statement about underlying topological spaces, not an
assertion that schematic images commute with arbitrary base change.

A closed range containing the original restricted range therefore contains
the restricted image. Injectivity of a projection on that closed range gives
injectivity on the actual restricted image, without reducedness assumptions.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {T A B C : Scheme.{u}} (f : T ⟶ A) [QuasiCompact f] (O : A.Opens)

/-- Open restriction commutes with closure of the original range. -/
lemma range_imageι_morphismRestrict :
    Set.range (f.imageι ∣_ O) = closure (Set.range (f ∣_ O)) := by
  have hr {X : Scheme.{u}} (g : X ⟶ A) :
      Set.range (g ∣_ O) = O.ι ⁻¹' Set.range g := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, (morphismRestrict_base_coe g O y).symm⟩
    · rintro ⟨y, hy⟩
      have hyO : y ∈ g ⁻¹ᵁ O := by
        change g y ∈ O
        rw [hy]
        exact x.property
      refine ⟨⟨y, hyO⟩, Subtype.ext ?_⟩
      exact (morphismRestrict_base_coe g O ⟨y, hyO⟩).trans hy
  rw [hr, hr]
  rw [IdealSheafData.range_subschemeι, Hom.support_ker]
  exact O.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    O.ι.continuous _

/-- A closed range containing the restricted original map contains the
restriction of its actual schematic-image inclusion. -/
lemma range_imageι_morphismRestrict_subset (c : C ⟶ O) [IsClosedImmersion c]
    (h : Set.range (f ∣_ O) ⊆ Set.range c) :
    Set.range (f.imageι ∣_ O) ⊆ Set.range c := by
  rw [range_imageι_morphismRestrict]
  exact closure_minimal h c.isClosedEmbedding.isClosed_range

/-- Injectivity on a containing closed range descends to the actual restricted
schematic image. No schematic factorization through that range is asserted. -/
lemma injective_imageι_morphismRestrict_comp (c : C ⟶ O) [IsClosedImmersion c]
    (p : O.toScheme ⟶ B) (h : Set.range (f ∣_ O) ⊆ Set.range c)
    (hc : Function.Injective (c ≫ p)) :
    Function.Injective ((f.imageι ∣_ O) ≫ p) := by
  intro x y hxy
  obtain ⟨a, ha⟩ := range_imageι_morphismRestrict_subset f O c h ⟨x, rfl⟩
  obtain ⟨b, hb⟩ := range_imageι_morphismRestrict_subset f O c h ⟨y, rfl⟩
  have hab : (c ≫ p) a = (c ≫ p) b := by
    simpa only [Hom.comp_apply, ha, hb] using hxy
  apply (f.imageι ∣_ O).isClosedEmbedding.injective
  rw [← ha, ← hb, hc hab]

/-- The resulting map is locally quasi-finite when it is locally of finite type. -/
lemma locallyQuasiFinite_imageι_morphismRestrict_comp (c : C ⟶ O)
    [IsClosedImmersion c] (p : O.toScheme ⟶ B)
    [LocallyOfFiniteType ((f.imageι ∣_ O) ≫ p)]
    (h : Set.range (f ∣_ O) ⊆ Set.range c)
    (hc : Function.Injective (c ≫ p)) :
    LocallyQuasiFinite ((f.imageι ∣_ O) ≫ p) :=
  LocallyQuasiFinite.of_injective
    (injective_imageι_morphismRestrict_comp f O c p h hc)

end AlgebraicGeometry.Scheme.Hom
