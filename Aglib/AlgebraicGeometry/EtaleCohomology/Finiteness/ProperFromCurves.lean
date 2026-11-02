/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProjectiveFromCurves.Relative
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.SurjectiveCompositionDescent
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Projective

/-! # Proper constructibility reduced to genuine curve families

The original Noetherian Chow construction produces a proper surjection with
projective source. Both its inner morphism and its composite with the original
proper map satisfy projective constructibility, using the actual closed graph
for the inner morphism. Reverse Leray and the original monic unit descend the
result; the cover is not asserted finite or acyclic. Affine-spectrum locality
then handles the arbitrary Noetherian target.

The sole geometric input left here is the full proper relative-curve
constructibility theorem. This is a reduction, not an unconditional proper
constructibility theorem, and uses neither proper base change nor a supplied
pencil or cohomological descent certificate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

variable
  (hcurve : ∀ {Y T : Scheme.{u}} [IsNoetherian T] (g : Y ⟶ T) [IsProper g],
    (∀ (K : Type u) [Field K] (η : Spec (.of K) ⟶ T),
      topologicalKrullDim (pullback g η : Scheme.{u}) ≤ 1) →
    ∀ (q : ℕ) (F : AbelianSheaf.{u, u + 1} Y), Constructible.IsConstructible F →
      Constructible.IsConstructible ((higherDirectImage g q).obj F))

include hcurve

/-- Original Chow geometry and the constructed surjective-composition degree
induction reduce arbitrary proper maps over a Noetherian ring to curves. -/
theorem higherDirectImage_properAffine_isConstructible_of_curves
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  obtain ⟨Y, p, n, j, V, hp, hs, hj, hbase, _, _⟩ :=
    Chow.exists_projective_modification R f
  have : IsProper p := hp
  have : Surjective p := hs
  have : IsClosedImmersion j := hj
  apply higherDirectImage_isConstructible_of_surjective_composition f p ?_ ?_ q F hF
  · intro k G hG
    exact higherDirectImage_projectiveSource_isConstructible_of_curves
      hcurve f p n j hbase k G hG
  · intro k G hG
    have h := higherDirectImage_closedProjective_isConstructible_of_curves
      hcurve R n j k G hG
    simpa only [hbase] using h

/-- The original arbitrary proper morphism over a Noetherian scheme is
reduced to the full relative-curve theorem by actual affine localization. -/
theorem higherDirectImage_proper_isConstructible_of_curves
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  apply higherDirectImage_isConstructible_of_affineSpecBaseChanges f q F
  intro U
  have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian U
  exact higherDirectImage_properAffine_isConstructible_of_curves hcurve Γ(S, U.1)
    (pullback.fst U.property.fromSpec f) q _
    (Constructible.isConstructible_pullback_of_qcqs (pullback.snd U.property.fromSpec f) hF)

end AlgebraicGeometry.Scheme.EtaleCohomology
