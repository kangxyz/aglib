/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian

/-!
# Actual projective pullbacks over an affine base

Every supplied Cartesian square of the original projective structural map
over a spectrum is canonically the polynomial projective space over its
actual ring. Both projections are retained. This applies, in particular,
to an affine-open restriction of a projective-space projection.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {R A : Type u} [CommRing R] [CommRing A] (ι : Type u)

/-- The base-change square written for the original morphism of spectra. -/
theorem isPullback_spec (g : Spec (.of A) ⟶ Spec (.of R)) :
    IsPullback (map (Spec.preimage g).hom ι) (toSpec A ι) (toSpec R ι) g := by
  simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using
    isPullback_map (Spec.preimage g).hom ι

variable {X : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (b : X ⟶ Spec (.of A))
  (g : Spec (.of A) ⟶ Spec (.of R)) (h : IsPullback a b (toSpec R ι) g)

/-- The canonical comparison for any original projective Cartesian square with affine base. -/
def affinePullbackIso : X ≅ ProjectiveSpace A ι :=
  h.isoIsPullback _ _ (isPullback_spec ι g)

@[reassoc (attr := simp)]
theorem affinePullbackIso_hom_map :
    (affinePullbackIso ι a b g h).hom ≫ map (Spec.preimage g).hom ι = a :=
  h.isoIsPullback_hom_fst _ _ (isPullback_spec ι g)

@[reassoc (attr := simp)]
theorem affinePullbackIso_hom_toSpec :
    (affinePullbackIso ι a b g h).hom ≫ toSpec A ι = b :=
  h.isoIsPullback_hom_snd _ _ (isPullback_spec ι g)

@[reassoc (attr := simp)]
theorem affinePullbackIso_inv_fst :
    (affinePullbackIso ι a b g h).inv ≫ a = map (Spec.preimage g).hom ι :=
  h.isoIsPullback_inv_fst _ _ (isPullback_spec ι g)

@[reassoc (attr := simp)]
theorem affinePullbackIso_inv_snd :
    (affinePullbackIso ι a b g h).inv ≫ b = toSpec A ι :=
  h.isoIsPullback_inv_snd _ _ (isPullback_spec ι g)

end AlgebraicGeometry.ProjectiveSpace
