/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.Etale
public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Sections of terminal etale covers over a strictly local ring -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.StrictlyLocal

universe u v

variable (R : Type u) [CommRing R] [HenselianLocalRing R]

private theorem exists_affine_section
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of A))
    (ht : t ≫ Spec.algebraMap R A = LocalRing.residueSpecMap R) :
    ∃ s : Spec (.of R) ⟶ Spec (.of A),
      s ≫ Spec.algebraMap R A = 𝟙 _ ∧ LocalRing.residueSpecMap R ≫ s = t := by
  have hself : Spec.algebraMap R R = 𝟙 (Spec (.of R)) := by
    simp [Spec.algebraMap]
  let a : A →ₐ[R] IsLocalRing.ResidueField R :=
    Spec.homEquivAlgHom ⟨t, ht⟩
  have ha : Spec.map (CommRingCat.ofHom a.toRingHom) = t :=
    congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨t, ht⟩)
  obtain ⟨b, hb⟩ := (HenselianLocalRing.residue_comp_bijective_of_etale R A).2 a
  refine ⟨Spec.map (CommRingCat.ofHom b.toRingHom), ?_, ?_⟩
  · simpa only [hself] using Spec.map_algHom_algebraMap b
  · calc
      _ = Spec.map (CommRingCat.ofHom a.toRingHom) := by
        dsimp only [LocalRing.residueSpecMap]
        rw [← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact congrArg AlgHom.toRingHom hb
      _ = t := ha

/-- An actual residue point of an arbitrary etale scheme over a henselian
local ring lifts to an actual section with its original residue triangle. -/
theorem exists_section_lift_of_residue_point
    {U : Scheme.{u}} (p : U ⟶ Spec (.of R)) [Etale p]
    (t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ U)
    (ht : t ≫ p = LocalRing.residueSpecMap R) :
    ∃ s : Spec (.of R) ⟶ U,
      s ≫ p = 𝟙 _ ∧ LocalRing.residueSpecMap R ≫ s = t := by
  obtain ⟨A, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
    (x := t.base default) (U := ⊤) (by simp)
  have hrange : Set.range t.base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x default]
  let t' := IsOpenImmersion.lift j t hrange
  have htj : t' ≫ j = t := IsOpenImmersion.lift_fac j t hrange
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ p)
  let : Algebra R A := g.hom.toAlgebra
  have hcoord : Spec.algebraMap R A = j ≫ p := hg
  have : Algebra.Etale R A := by
    have he : Etale (Spec.algebraMap R A) := by
      rw [hcoord]
      infer_instance
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale.{u})).mp he)
  have htp : t' ≫ Spec.algebraMap R A = LocalRing.residueSpecMap R := by
    rw [hcoord, ← Category.assoc, htj, ht]
  obtain ⟨s, hs, hred⟩ := exists_affine_section R A t' htp
  refine ⟨s ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← hcoord, hs]
  · rw [← Category.assoc, hred, htj]

variable [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Some member of any jointly surjective family of etale maps to the
terminal scheme has an actual section. The residue field need not be perfect. -/
theorem exists_section_of_etale_family
    {ι : Type v} (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ Spec (.of R))
    [∀ i, Etale (p i)]
    (h : ∀ x : Spec (.of R), ∃ (i : ι) (y : U i), p i y = x) :
    ∃ (i : ι) (s : Spec (.of R) ⟶ U i), s ≫ p i = 𝟙 _ := by
  obtain ⟨i, y, hy⟩ := h ((LocalRing.residueSpecMap R) default)
  obtain ⟨t, ht, _⟩ := exists_fac_of_etale_of_isSepClosed (p i)
    (LocalRing.residueSpecMap R) y hy
  obtain ⟨s, hs, _⟩ := exists_section_lift_of_residue_point R (p i) t ht
  exact ⟨i, s, hs⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.StrictlyLocal
