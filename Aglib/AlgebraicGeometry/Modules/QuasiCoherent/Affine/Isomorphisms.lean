/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Affine quasicoherent isomorphisms

An isomorphism on global sections detects an isomorphism between quasicoherent module sheaves on
an affine scheme, through the canonical fromTildeΓ comparisons.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/AffineApproximation.lean`.
SHA-256: `2029b40cd181d56164f97a019526a3e93de58da78ca2ad65b0f9b33ad9b3ef18`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Global sections reflect isomorphisms between actual quasicoherent
sheaves on an affine scheme. -/
theorem affine_isIso_of_globalSections (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [IsIso (moduleSpecΓFunctor.map f)] : IsIso f := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  have he : (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := Scheme.Modules.fromTildeΓNatTrans.naturality f
  rw [← isIso_comp_left_iff M.fromTildeΓ f, ← he]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
