/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# The spectrum of an extension field over the original base

Source: packet R5Lab.Aglib.AlgebraicGeometry.RationalPoints.ExtensionSource.
The forward structural morphism is exactly Spec.map of the given field map.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.OverField
universe u
variable {k K : Type u} [Field k] [Field K]

/-- Spec K with the structural map induced by the given field homomorphism. -/
abbrev extensionPointSource (f : k →+* K) : FScheme k :=
  Over.mk (Spec.map (CommRingCat.ofHom f))

@[simp] theorem extensionPointSource_hom (f : k →+* K) :
    (extensionPointSource f).hom = Spec.map (CommRingCat.ofHom f) := rfl

end AlgebraicGeometry.Scheme.OverField
