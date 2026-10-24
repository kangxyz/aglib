/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.DiscreteDecomposition
public import Mathlib.AlgebraicGeometry.Artinian

/-! # Actual stalk rings of locally Artinian schemes

The statement is local: no quasi-compactness or finiteness of the set of points
is needed. The actual local-spectrum map is an open immersion, so its original
stalk ring is Artinian without replacing the scheme by its reduction.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme

universe u

/-- Actual stalk rings are Artinian on every locally Artinian scheme, without
any global quasi-compactness hypothesis. -/
theorem stalk_isArtinian_of_isLocallyArtinian (X : Scheme.{u})
    [IsLocallyArtinian X] (x : X) : IsArtinianRing (X.presheaf.stalk x) := by
  let : IsOpenImmersion (X.fromSpecStalk x) := fromSpecStalk_isOpenImmersion_of_discrete X x
  let : IsLocallyArtinian (Spec (X.presheaf.stalk x)) :=
    IsLocallyArtinian.of_isImmersion (X.fromSpecStalk x)
  exact Scheme.isLocallyArtinianScheme_Spec.mp inferInstance

end AlgebraicGeometry.Scheme
