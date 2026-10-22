/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import Aglib.RingTheory.ReesAlgebra.Map

/-!
# Closed immersions of blowups along inverse-image centres

The comparison is the existing `BaseChange.map`, with its original base
triangle. The affine proof uses the actual coefficientwise Rees map and
native Proj functor. It does not identify blowup with a nonflat base change.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Scheme.Blowup

variable {A R : Type u} [CommRing A] [CommRing R]

/-- The coefficientwise Rees map induces the original affine blowup comparison. -/
def affineClosedComparison (f : A →+* R) (hf : Function.Surjective f) (I : Ideal A) :
    affineProj (I.map f) ⟶ affineProj I :=
  Proj.map (reesAlgebra.map f I) (reesAlgebra.irrelevant_le_map f hf I)

theorem affineClosedComparison_isClosedImmersion (f : A →+* R)
    (hf : Function.Surjective f) (I : Ideal A) :
    IsClosedImmersion (affineClosedComparison f hf I) :=
  Proj.map_isClosedImmersion_of_degreewise_surjective _ _
    (reesAlgebra.map_degreewise_surjective f hf I)

/-- The Proj map retains the literal original coefficient-ring triangle. -/
@[reassoc]
theorem affineClosedComparison_map (f : A →+* R) (hf : Function.Surjective f)
    (I : Ideal A) :
    affineClosedComparison f hf I ≫ affineProjMap I =
      affineProjMap (I.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  let F := reesAlgebra.map f I
  let hF := reesAlgebra.irrelevant_le_map f hf I
  apply (Proj.mapAffineOpenCover F hF).openCover.hom_ext
  intro s
  change (n : ℕ+) × ↥(reesAlgebra.grading I (n : ℕ)) at s
  rcases s with ⟨⟨n, hn⟩, ⟨r, hr⟩⟩
  change r ∈ reesAlgebra.grading I n at hr
  change Proj.awayι _ (F r) (F.map_mem hr) hn ≫
      Proj.map F hF ≫ affineProjMap I =
    Proj.awayι _ (F r) (F.map_mem hr) hn ≫
      affineProjMap (I.map f) ≫ Spec.map (CommRingCat.ofHom f)
  refine (Proj.awayι_comp_map_assoc F hF hn r hr (affineProjMap I)).trans ?_
  simp only [affineProjMap, Category.assoc, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp]
  apply congrArg (fun g : CommRingCat.of A ⟶
    CommRingCat.of (Away (reesAlgebra.grading (I.map f)) (F r)) => Spec.map g)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change Away.map F r (fromZeroRingHom _ _ ((reesAlgebra.degreeZeroEquiv I).symm a)) =
    fromZeroRingHom _ _ ((reesAlgebra.degreeZeroEquiv (I.map f)).symm (f a))
  apply HomogeneousLocalization.val_injective
  change (Localization.mk (F ((reesAlgebra.degreeZeroEquiv I).symm a)) ⟨F 1, _⟩ :
      Localization (Submonoid.powers (F r))) =
    Localization.mk
      (((reesAlgebra.degreeZeroEquiv (I.map f)).symm (f a)) : reesAlgebra (I.map f))
      ⟨1, _⟩
  have hc : F (algebraMap A (reesAlgebra I) a) =
      algebraMap R (reesAlgebra (I.map f)) (f a) := by
    apply Subtype.ext
    exact Polynomial.map_C f
  simp only [map_one, reesAlgebra.degreeZeroEquiv_symm_coe, hc]

/-- Closedness for every universal representative, not just the native affine Proj. -/
theorem BaseChange.map_isClosedImmersion_affineCenter (f : A →+* R)
    (hf : Function.Surjective f) (I : Ideal A)
    (B : BlowupDatum (affineCenter A I))
    (C : BlowupDatum (affineCenter R (I.map f))) :
    IsClosedImmersion (BaseChange.map (Spec.map (CommRingCat.ofHom f))
      (BaseChange.affineCenter_comap f I) B C) := by
  let B₀ := affineProjBlowupDatum I
  let C₀ := affineProjBlowupDatum (I.map f)
  let α : C₀.Y ⟶ B₀.Y := affineClosedComparison f hf I
  let : IsClosedImmersion α := affineClosedComparison_isClosedImmersion f hf I
  have hα : α ≫ B₀.map = C₀.map ≫ Spec.map (CommRingCat.ofHom f) :=
    affineClosedComparison_map f hf I
  have hmap : BaseChange.map (Spec.map (CommRingCat.ofHom f))
      (BaseChange.affineCenter_comap f I) B C =
      (C.comparisonIso C₀).hom ≫ α ≫
        (B₀.comparisonIso B).hom := by
    symm
    apply BaseChange.map_unique
    rw [Category.assoc, Category.assoc, BlowupDatum.comparisonIso_hom_map]
    rw [hα, ← Category.assoc]
    exact congrArg (fun g => g ≫ Spec.map (CommRingCat.ofHom f))
      (C.comparisonIso_hom_map C₀)
  rw [hmap]
  infer_instance

end AlgebraicGeometry.Scheme.Blowup
