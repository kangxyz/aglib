/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Base change into an actual isomorphism open

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Isomorphism/OpenPullback.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `96effc7d6cd3002b45c20659ffe31a70615b00ff822b83c492db6fbf979a85b6`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An actual base change of a morphism is an isomorphism whenever the base
change lands in an open on which the canonical restriction is an isomorphism. -/
lemma isIso_pullback_of_range_subset {Y X T : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] (t : T ⟶ X) (ht : Set.range t ⊆ U) :
    IsIso (pullback.snd f t) := by
  let t' : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι t (by simpa using ht)
  have ht' : t' ≫ U.ι = t := IsOpenImmersion.lift_fac _ _ _
  have ha : Set.range (pullback.fst f t) ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (pullback.fst f t ≫ f) z ∈ U
    rw [pullback.condition]
    exact ht ⟨_, rfl⟩
  let a := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (pullback.fst f t) ha
  have ha' : a ≫ (f ⁻¹ᵁ U).ι = pullback.fst f t := IsOpenImmersion.lift_fac _ _ _
  have htotal : IsPullback (pullback.snd f t) (a ≫ (f ⁻¹ᵁ U).ι)
      (t' ≫ U.ι) f := by rw [ha', ht']; exact (IsPullback.of_hasPullback f t).flip
  have hw : pullback.snd f t ≫ t' = a ≫ (f ∣_ U) := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, ht', Category.assoc, morphismRestrict_ι, ← Category.assoc, ha']
    exact pullback.condition.symm
  have hpb := (IsPullback.of_bot htotal hw (isPullback_morphismRestrict f U)).flip
  exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
    hpb inferInstance

end AlgebraicGeometry.Scheme.Hom
