/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.OpenLocalization

/-!
# Local quasi-finiteness of an actual graph-image projection

The image is the schematic image of a single original map, not a product of
separate graph closures. On an open cover of its ambient scheme, a containing
closed range with injective projection forces the image projection to be
locally quasi-finite. In the quasi-domination application these closed ranges
are the actual local extended section graphs after a common modification.
Protected opens and their admissible modifications remain upstream of this
local criterion. No finiteness of the indexing type is needed here.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- Local closed graphs with injective projection control the projection of
the single original schematic image. The finite-type hypothesis is on that
actual projection, and all original-range containments are retained. -/
theorem locallyQuasiFinite_image_projection_of_closed_ranges
    {T A B : Scheme.{u}} (f : T ⟶ A) [QuasiCompact f] (p : A ⟶ B)
    [LocallyOfFiniteType (f.imageι ≫ p)]
    {ι : Type v} (O : ι → A.Opens) (hcover : (⨆ i, O i) = ⊤)
    (D : ι → Scheme.{u}) (c : ∀ i, D i ⟶ (O i).toScheme)
    [∀ i, IsClosedImmersion (c i)]
    (hrange : ∀ i, Set.range (f ∣_ O i) ⊆ Set.range (c i))
    (hinj : ∀ i, Function.Injective (c i ≫ (O i).ι ≫ p)) :
    LocallyQuasiFinite (f.imageι ≫ p) := by
  have : IsZariskiLocalAtSource @LocallyQuasiFinite :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyQuasiFinite)
      (Q := RingHom.QuasiFinite)
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (fun i => f.imageι ⁻¹ᵁ O i) (f.imageι.iSup_preimage_eq_top hcover)
  intro i
  have he : (f.imageι ∣_ O i) ≫ ((O i).ι ≫ p) =
      (f.imageι ⁻¹ᵁ O i).ι ≫ (f.imageι ≫ p) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have : LocallyOfFiniteType ((f.imageι ∣_ O i) ≫ ((O i).ι ≫ p)) := by
    rw [he]
    infer_instance
  have h := f.locallyQuasiFinite_imageι_morphismRestrict_comp
    (O i) (c i) ((O i).ι ≫ p) (hrange i) (hinj i)
  rwa [he] at h

end AlgebraicGeometry.Scheme.QuasiDomination
