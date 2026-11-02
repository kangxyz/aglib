/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusPoints
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentGenerization
public import Aglib.AlgebraicGeometry.Spec.SpecializationValuation

/-! # Generization stability of the original smooth section-component locus

Original specializations are realized by valuation subrings of their original
residue fields. The original pullback has two actual sections. Exact locus
base change and the normal-domain two-section theorem carry membership to
the original generizing point. No Noetherian or DVR assumption is used.
-/

@[expose] public noncomputable section
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
open PrincipalNeighborhoodLimit
universe u

/-- The whole normal-domain two-section argument in the original locus,
before a particular valuation spectrum or original point is supplied. -/
private theorem section_generic_point_mem_locus
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [Smooth p]
    (σ τ : Spec (.of R) ⟶ Y) (hσ : σ ≫ p = 𝟙 _) (hτ : τ ≫ p = 𝟙 _)
    (s : Spec (.of R)) (hs : τ s ∈ sectionComponentLocus p σ hσ) :
    τ (Spec.algebraMap R K (IsLocalRing.closedPoint K)) ∈ sectionComponentLocus p σ hσ := by
  let b := Spec.algebraMap R K
  let g := pullback.fst p b
  let q := pullback.snd p b
  let σK := localizationSection p σ hσ K
  let τK := localizationSection p τ hτ K
  let η : Spec (.of K) := IsLocalRing.closedPoint K
  have hσK : σK ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hσg : σK ≫ g = b ≫ σ := pullback.lift_fst _ _ _
  have hτg : τK ≫ g = b ≫ τ := pullback.lift_fst _ _ _
  have hc := generic_sections_mem_connectedComponent_of_fiber R K p σ τ hσ hτ s
    ((section_point_mem_sectionComponentLocus_iff p σ τ hσ hτ s).mp hs)
  have hm : τK η ∈ sectionComponentLocus q σK hσK := by
    rw [sectionComponentLocus_eq_connectedComponent_of_field K q σK hσK]
    exact hc
  have hpre := sectionComponentLocus_preimage_of_isPullback p g q b
    (.of_hasPullback p b) σ hσ σK hσK hσg
  have hmem : g (τK η) ∈ sectionComponentLocus p σ hσ := by
    change τK η ∈ g ⁻¹' sectionComponentLocus p σ hσ
    rw [hpre]
    exact hm
  have he := congrArg (fun a : Spec (.of K) ⟶ Y => a η) hτg
  change g (τK η) = τ (b η) at he
  exact he ▸ hmem

/-- The actual smooth fibrewise section-component locus is stable under
arbitrary generization. Both points and all residue maps are the originals. -/
theorem sectionComponentLocus_stableUnderGeneralization
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    StableUnderGeneralization (sectionComponentLocus f σ hσ) := by
  intro x y hyx hx
  obtain ⟨A, a, ha, hclosed⟩ := exists_valuationSubring_of_specializes X hyx
  let K := X.residueField y
  let b : Spec (.of A) ⟶ S := a ≫ f
  let P := pullback f b
  let g : P ⟶ X := pullback.fst f b
  let p : P ⟶ Spec (.of A) := pullback.snd f b
  let σA : Spec (.of A) ⟶ P := pullback.lift (b ≫ σ) (𝟙 _) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  let τA : Spec (.of A) ⟶ P := pullback.lift a (𝟙 _) (by
    rw [Category.id_comp])
  have hσA : σA ≫ p = 𝟙 _ := pullback.lift_snd _ _ _
  have hτA : τA ≫ p = 𝟙 _ := pullback.lift_snd _ _ _
  have hσg : σA ≫ g = b ≫ σ := pullback.lift_fst _ _ _
  have hτg : τA ≫ g = a := pullback.lift_fst _ _ _
  have hpre := sectionComponentLocus_preimage_of_isPullback f g p b
    (.of_hasPullback f b) σ hσ σA hσA hσg
  have hpoint (t : Spec (.of A)) : g (τA t) = a t :=
    congrArg (fun c : Spec (.of A) ⟶ X => c t) hτg
  let s : Spec (.of A) := IsLocalRing.closedPoint A
  have hclosed' : a s = x := hclosed
  have hclosedA : τA s ∈ sectionComponentLocus p σA hσA := by
    rw [← hpre]
    change g (τA s) ∈ sectionComponentLocus f σ hσ
    rw [hpoint, hclosed']
    exact hx
  have hgeneric := section_generic_point_mem_locus A K p σA τA hσA hτA
    s hclosedA
  let η : Spec (.of K) := IsLocalRing.closedPoint K
  have hmem : a (Spec.algebraMap A K η) ∈ sectionComponentLocus f σ hσ := by
    rw [← hpoint]
    change τA (Spec.algebraMap A K η) ∈ g ⁻¹' sectionComponentLocus f σ hσ
    rw [hpre]
    exact hgeneric
  have he := congrArg (fun c : Spec (.of K) ⟶ X => c η) ha
  change a (Spec.algebraMap A K η) = X.fromSpecResidueField y η at he
  have hey : a (Spec.algebraMap A K η) = y :=
    he.trans (X.fromSpecResidueField_apply y η)
  exact hey ▸ hmem

end AlgebraicGeometry.Scheme
