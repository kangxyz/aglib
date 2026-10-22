/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GradedAlgebra.HomogeneousLocalization.Surjective
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions from degreewise-surjective graded maps

The morphism is the native `Proj.map`. Its literal basic-open preimages and
native homogeneous-localization maps identify every restriction with the
spectrum of a surjective ring map. No finite generation is needed.
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization Graded

universe u

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The actual Proj map is closed when the original map is surjective in every degree. -/
theorem map_isClosedImmersion_of_degreewise_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hsurj : ∀ n, Function.Surjective (f.gradedAddHom n)) :
    IsClosedImmersion (map f hf) := by
  let U := fun a : Σ n : ℕ+, 𝒜 (n : ℕ) => basicOpen 𝒜 (a.2 : A)
  have hcover : iSup U = ⊤ := by
    let (a : Σ n : ℕ+, 𝒜 (n : ℕ)) :
        IsOpenImmersion ((affineOpenCover 𝒜).openCover.f a) :=
      (affineOpenCover 𝒜).openCover.map_prop a
    have hopen (a : Σ n : ℕ+, 𝒜 (n : ℕ)) :
        ((affineOpenCover 𝒜).openCover.f a).opensRange = U a :=
      opensRange_awayι 𝒜 (a.2 : A) a.2.property a.1.property
    have h := (affineOpenCover 𝒜).openCover.iSup_opensRange
    change (⨆ a : Σ n : ℕ+, 𝒜 (n : ℕ),
      ((affineOpenCover 𝒜).openCover.f a).opensRange) = ⊤ at h
    exact (congrArg iSup (funext hopen)).symm.trans h
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) U hcover
  intro a
  have hpre : map f hf ⁻¹ᵁ U a = basicOpen ℬ (f a.2) :=
    map_preimage_basicOpen f hf a.2
  let eS := (Proj ℬ).isoOfEq hpre ≪≫
    basicOpenIsoSpec ℬ (f a.2) (map_mem f a.2.property) a.1.property
  let eT := basicOpenIsoSpec 𝒜 (a.2 : A) a.2.property a.1.property
  let φ := Spec.map (CommRingCat.ofHom (Away.map f (a.2 : A)))
  let hφ : IsClosedImmersion φ := IsClosedImmersion.spec_of_surjective _
    (Away.map_surjective_of_degreewise_surjective f hsurj a.2.property)
  have hfac : eS.inv ≫ (map f hf ∣_ U a) = φ ≫ eT.inv := by
    apply (cancel_mono (U a).ι).mp
    simp only [eS, Iso.trans_inv, Category.assoc, morphismRestrict_ι,
      Scheme.isoOfEq_inv_ι_assoc]
    dsimp only [φ, eT, U]
    rw [← Category.assoc]
    exact awayι_comp_map f hf a.1.property (a.2 : A) a.2.property
  have he : (map f hf ∣_ U a) = eS.hom ≫ φ ≫ eT.inv := by
    rw [← hfac]
    simp
  rw [he]
  infer_instance

end AlgebraicGeometry.Proj
