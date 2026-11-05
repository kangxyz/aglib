/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusRestriction
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentAffinePullback

/-! # Original-section component restriction with affine field fibres

The supplied affine-field-fibre invariant passes to the actual open component
of the original section. The Noetherian affine base need not be local. The
construction proves connectedness and retains the entire original section;
it does not assume connectedness of the original family or manufacture the
affine-field-fibre invariant.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- A smooth qcqs family with affine field fibres over a Noetherian affine
base admits its actual geometrically connected component restriction through
the whole given section, with that same section and affine field fibres. -/
theorem exists_noetherian_sectionComponent_restriction_affine_fibers
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [QuasiCompact f] [QuasiSeparated f]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (haff : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec (.of R)),
      IsAffine (pullback f b : Scheme.{u})) :
    ∃ (W : X.Opens) (τ : Spec (.of R) ⟶ W.toScheme),
      (W : Set X) = sectionComponentLocus f σ hσ ∧
      τ ≫ W.ι = σ ∧ τ ≫ (W.ι ≫ f) = 𝟙 _ ∧
      SmoothOfRelativeDimension n (W.ι ≫ f) ∧
      QuasiCompact (W.ι ≫ f) ∧ QuasiSeparated (W.ι ≫ f) ∧
      GeometricallyConnected (W.ι ≫ f) ∧
      ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec (.of R)),
        IsAffine (pullback (W.ι ≫ f) b : Scheme.{u}) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨W, τ, hW, hτ, hτf, hgc, hqc⟩ :=
    exists_noetherian_sectionComponent_restriction R f n σ hσ
  have hsm : SmoothOfRelativeDimension n (W.ι ≫ f) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (W.ι ≫ f))
  have hqs : QuasiSeparated (W.ι ≫ f) := inferInstance
  refine ⟨W, τ, hW, hτ, hτf, hsm, hqc, hqs, hgc, ?_⟩
  intro K _ b
  let : IsAffine (pullback f b : Scheme.{u}) := haff K b
  exact sectionComponent_fieldPullback_isAffine_of_isAffine_pullback
    f σ hσ W hW K b

end AlgebraicGeometry.Scheme
