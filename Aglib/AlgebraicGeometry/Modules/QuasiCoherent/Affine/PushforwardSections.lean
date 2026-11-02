/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward

/-! # Evaluation of the native affine pushforward section comparison

This shared section formula is used by original presentation units and affine
chart coordinate sections. It retains the original coefficient and comparison.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation of the native affine pushforward section comparison is the
original coefficient evaluated on the whole affine source. -/
theorem moduleSpecΓFunctor_map_pushforwardGlobalSectionsIso_apply
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : (Spec R).Modules} {N : (Spec S).Modules}
    (q : M ⟶ (pushforward (Spec.map φ)).obj N)
    (m : moduleSpecΓFunctor.obj M) :
    (moduleSpecΓFunctor.map q ≫ (pushforwardGlobalSectionsIso φ).hom.app N) m =
      q.app ⊤ m := rfl


end AlgebraicGeometry.Scheme.Modules
