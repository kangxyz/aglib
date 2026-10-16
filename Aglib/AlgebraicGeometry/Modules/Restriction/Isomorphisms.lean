/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Isomorphisms under open restriction

Restricting farther preserves an isomorphism on an open, and restriction along an open immersion
detects the corresponding isomorphism on its open range.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/ObjectExtensionAux.lean`.
SHA-256: `f5bd944f0a65c3201e86983e54d0b9d8776089297edbb495dbca711f5f6bb1dc`.
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
namespace AlgebraicGeometry.Scheme.Modules

/-- An isomorphism on an open remains an isomorphism on every smaller open. -/
theorem isIso_restrict_map_of_le
    {X : Scheme.{u}} {W V : X.Opens} (h : W ≤ V)
    {M N : X.Modules} (s : M ⟶ N)
    [IsIso ((restrictFunctor V.ι).map s)] :
    IsIso ((restrictFunctor W.ι).map s) := by
  let e : restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h) ≅
      restrictFunctor W.ι :=
    (restrictFunctorComp (X.homOfLE h) V.ι).symm ≪≫
      restrictFunctorCongr (X.homOfLE_ι h)
  apply (NatIso.isIso_map_iff e s).mp
  exact (restrictFunctor (X.homOfLE h)).map_isIso ((restrictFunctor V.ι).map s)

/-- Restriction along an open immersion and along its actual range have the
same isomorphism-detection property. -/
theorem isIso_restrict_map_of_opensRange
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (s : M ⟶ N)
    [IsIso ((restrictFunctor j.opensRange.ι).map s)] :
    IsIso ((restrictFunctor j).map s) := by
  let e : restrictFunctor j.opensRange.ι ⋙ restrictFunctor j.isoOpensRange.hom ≅
      restrictFunctor j :=
    (restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).symm ≪≫
      restrictFunctorCongr j.isoOpensRange_hom_ι
  apply (NatIso.isIso_map_iff e s).mp
  exact (restrictFunctor j.isoOpensRange.hom).map_isIso
    ((restrictFunctor j.opensRange.ι).map s)

end AlgebraicGeometry.Scheme.Modules
