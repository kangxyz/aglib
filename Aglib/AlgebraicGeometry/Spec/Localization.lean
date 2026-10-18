/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Localization
public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Spec
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Canonical localization squares on spectra

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open LinearMap

section
namespace AlgebraicGeometry.Scheme

variable {R A B : CommRingCat.{u}}

/-- On spectra the same canonical square is cartesian. -/
theorem isPullback_specMap_localizationAway (φ : A ⟶ B) (s : A) :
    IsPullback (Spec.map ((CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away s)
      (Localization.Away (φ s)) φ.hom s))))
      (Spec.map ((CommRingCat.ofHom (algebraMap B (Localization.Away (φ s))))))
      (Spec.map ((CommRingCat.ofHom (algebraMap A (Localization.Away s))))) (Spec.map φ) := by
  apply IsOpenImmersion.isPullback
  · rw [← Spec.map_comp, ← Spec.map_comp, CommRingCat.localizationAway_map_comm]
  · simp only [Scheme.Hom.opensRange_localizationAway]
    exact SpecMap_preimage_basicOpen φ s

/-- The localized quotient remains a closed immersion. -/
theorem isClosedImmersion_specMap_localizationAway (φ : A ⟶ B) (s : A)
    [IsClosedImmersion (Spec.map φ)] : IsClosedImmersion (Spec.map ((CommRingCat.ofHom
      (IsLocalization.Away.map (Localization.Away s) (Localization.Away (φ s)) φ.hom s)))) :=
  IsClosedImmersion.spec_of_surjective _ ((IsLocalization.map_surjective_of_surjective
    (Submonoid.powers s) (Localization.Away s) (Localization.Away (φ s))
    (IsClosedImmersion.surjective_of_specMap φ)))

/-- The quotient-to-base map is the original projection precomposed with the
canonical open immersion of its localized source. -/
theorem specMap_localizationAway_comp (ψ : R ⟶ A) (φ : A ⟶ B) (s : A) :
    Spec.map ((CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away s) (Localization.Away
      (φ s)) φ.hom s))) ≫ Spec.map ((ψ ≫ CommRingCat.ofHom (algebraMap A (Localization.Away s)))) =
      Spec.map ((CommRingCat.ofHom (algebraMap B (Localization.Away (φ s))))) ≫ (Spec.map φ ≫
        Spec.map ψ) := by
  rw [Spec.map_comp, ← Category.assoc, ← Spec.map_comp,
    CommRingCat.localizationAway_map_comm, Spec.map_comp, Category.assoc]

/-- Local quasi-finiteness survives the ambient principal-open restriction. -/
theorem locallyQuasiFinite_specMap_localizationAway_comp (ψ : R ⟶ A) (φ : A ⟶ B) (s : A)
    [LocallyQuasiFinite (Spec.map φ ≫ Spec.map ψ)] :
    LocallyQuasiFinite (Spec.map ((CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away s)
      (Localization.Away (φ s)) φ.hom s))) ≫ Spec.map ((ψ ≫ CommRingCat.ofHom (algebraMap A
      (Localization.Away s))))) := by
  rw [_root_.AlgebraicGeometry.Scheme.specMap_localizationAway_comp]
  infer_instance

/-- Flatness survives the ambient principal-open restriction. -/
theorem flat_specMap_localizationAway_comp (ψ : R ⟶ A) (φ : A ⟶ B) (s : A)
    [Flat (Spec.map φ ≫ Spec.map ψ)] :
    Flat (Spec.map ((CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away s)
      (Localization.Away (φ s)) φ.hom s))) ≫ Spec.map ((ψ ≫ CommRingCat.ofHom (algebraMap A
      (Localization.Away s))))) := by
  rw [_root_.AlgebraicGeometry.Scheme.specMap_localizationAway_comp]
  infer_instance

/-- Local finite presentation survives the ambient principal-open restriction. -/
theorem locallyOfFinitePresentation_specMap_localizationAway_comp (ψ : R ⟶ A) (φ : A ⟶ B) (s : A)
    [LocallyOfFinitePresentation (Spec.map φ ≫ Spec.map ψ)] :
    LocallyOfFinitePresentation
      (Spec.map ((CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away s)
        (Localization.Away (φ s)) φ.hom s))) ≫ Spec.map ((ψ ≫ CommRingCat.ofHom (algebraMap A
        (Localization.Away s))))) := by
  rw [_root_.AlgebraicGeometry.Scheme.specMap_localizationAway_comp]
  infer_instance

end AlgebraicGeometry.Scheme
end
