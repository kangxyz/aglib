/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian

/-!
# The base-change isomorphism over the new base

For `σ : A →+* B`, the identification `baseChangeIso σ ι : P^n_B ≅ P^n_A ×_{Spec A} Spec B` of
`Cartesian` lies over `Spec B`:

* `ProjectiveSpace.baseChangeIso_inv_toSpec`: its inverse followed by `toSpec B ι` is the second
  projection of the fibre product;
* `ProjectiveSpace.baseChangeIso_hom_appTop_comp`: the same on global sections, for the
  structural ring maps `B → Γ(P^n_A ×_{Spec A} Spec B)` and `B → Γ(P^n_B)` through
  `Scheme.ΓSpecIso`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The identification `X_B ≅ P^n_B` lies over `Spec B`. -/
theorem baseChangeIso_inv_toSpec (σ : A →+* B) (ι : Type u) :
    (baseChangeIso σ ι).inv ≫ toSpec B ι =
      pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)) := by
  rw [← baseChangeIso_hom_snd σ ι, Iso.inv_hom_id_assoc]

/-- The structural ring map of `X_B` over `Spec B`, followed by the global-section map of
`baseChangeIso σ ι`, is the structural ring map of `P^n_B`. -/
theorem baseChangeIso_hom_appTop_comp (σ : A →+* B) (ι : Type u) :
    (baseChangeIso σ ι).hom.appTop.hom.comp
        ((pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) =
      (toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom := by
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    baseChangeIso_hom_snd]

end AlgebraicGeometry.ProjectiveSpace
