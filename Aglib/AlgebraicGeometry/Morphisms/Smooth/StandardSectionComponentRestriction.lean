/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.StandardSectionComponentOpen

/-! # The actual standard-affine section-component restriction

Over an arbitrary base ring, the proved openness of the unique original
locus supplies its actual open restriction, original section triangles,
quasi-compactness, quasi-separatedness and geometrically connected smooth
structural map. The point condition remains membership of that same locus;
no coverage of unrelated prescribed points is assumed or asserted.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme
universe u

/-- The original standard-affine family admits the actual section-component
restriction with all structural properties and exact original point membership. -/
theorem exists_standardSectionComponent_restriction
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R B]
    (σ : B →ₐ[R] R)
    (hσ : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.algebraMap R B = 𝟙 _) :
    ∃ (W : (Spec (.of B)).Opens) (τ : Spec (.of R) ⟶ W.toScheme),
      (W : Set (Spec (.of B))) = sectionComponentLocus (Spec.algebraMap R B)
        (Spec.map (CommRingCat.ofHom σ.toRingHom)) hσ ∧
      τ ≫ W.ι = Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
      τ ≫ (W.ι ≫ Spec.algebraMap R B) = 𝟙 _ ∧
      SmoothOfRelativeDimension n (W.ι ≫ Spec.algebraMap R B) ∧
      QuasiCompact (W.ι ≫ Spec.algebraMap R B) ∧
      QuasiSeparated (W.ι ≫ Spec.algebraMap R B) ∧
      GeometricallyConnected (W.ι ≫ Spec.algebraMap R B) ∧
      UniversallyOpen (W.ι ≫ Spec.algebraMap R B) ∧
      ∀ x : Spec (.of B),
        x ∈ sectionComponentLocus (Spec.algebraMap R B)
          (Spec.map (CommRingCat.ofHom σ.toRingHom)) hσ ↔
        ∃ w : W.toScheme, W.ι w = x := by
  let f : Spec (.of B) ⟶ Spec (.of R) := Spec.algebraMap R B
  let σS : Spec (.of R) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let : SmoothOfRelativeDimension n f := by
    change SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨hopen, hretro⟩ := standardSectionComponentLocus_isOpen_isRetrocompact R B n σ hσ
  let W := sectionComponentOpen f σS hσ hopen
  obtain ⟨τ, hτ, hτf⟩ := exists_sectionComponentOpen_section f σS hσ hopen
  let : QuasiCompact W.ι := sectionComponentOpen_quasiCompact_ι f σS hσ hopen hretro
  have hsm : SmoothOfRelativeDimension n (W.ι ≫ f) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (W.ι ≫ f))
  let : SmoothOfRelativeDimension n (W.ι ≫ f) := hsm
  let : Smooth (W.ι ≫ f) := SmoothOfRelativeDimension.smooth n (W.ι ≫ f)
  refine ⟨W, τ, rfl, hτ, hτf, hsm, inferInstance, inferInstance,
    sectionComponentOpen_geometricallyConnected f σS hσ hopen, inferInstance, ?_⟩
  intro x
  change x ∈ W ↔ x ∈ Set.range W.ι
  rw [Opens.range_ι]
  rfl

end AlgebraicGeometry.Scheme
