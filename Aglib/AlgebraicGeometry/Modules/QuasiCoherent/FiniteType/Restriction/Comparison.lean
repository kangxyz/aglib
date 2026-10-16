/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison

/-!
# Finite-type restriction comparisons

Finite type passes from an open immersion to its open range and is detected on the top open. The
principal restriction comparison uses the actual affine finite-type equivalences and restriction
functors.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/Gluing.lean`.
SHA-256: `6aaa5fe7afa5e725eb43e457c3c85cd644113f236df923a0ead266175ea61559`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/ObjectExtensionAux.lean`.
SHA-256: `f5bd944f0a65c3201e86983e54d0b9d8776089297edbb495dbca711f5f6bb1dc`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/PrincipalRestriction.lean`.
SHA-256: `7406934ff4707a5c3be34e57ffcf420758a1cbec35455aa99406b13c2008eec8`.
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

/-- Finite-type quasicoherence along an open immersion transfers to its
actual open range. -/
theorem affineLocallyFiniteType_restrict_opensRange
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (h : affineLocallyFiniteType U (M.restrict j)) :
    affineLocallyFiniteType j.opensRange.toScheme (M.restrict j.opensRange.ι) := by
  let e : (M.restrict j).restrict j.isoOpensRange.inv ≅
      M.restrict j.opensRange.ι :=
    ((Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp).app M
  exact (affineLocallyFiniteType j.opensRange.toScheme).prop_of_iso e
    (affineLocallyFiniteType_restrict j.isoOpensRange.inv h)

/-- Finite-type quasicoherence on the top open transfers to the scheme itself. -/
theorem affineLocallyFiniteType_of_restrict_top
    {X : Scheme.{u}} (M : X.Modules)
    (h : affineLocallyFiniteType (⊤ : X.Opens).toScheme (M.restrict (⊤ : X.Opens).ι)) :
    affineLocallyFiniteType X M := by
  let e : (M.restrict (⊤ : X.Opens).ι).restrict X.topIso.inv ≅ M :=
    ((restrictFunctorComp X.topIso.inv (⊤ : X.Opens).ι).app M).symm ≪≫
      (restrictFunctorCongr X.toIso_inv_ι).app M ≪≫ restrictFunctorId.app M
  exact (affineLocallyFiniteType X).prop_of_iso e (affineLocallyFiniteType_restrict X.topIso.inv h)

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- The global/affine comparison square for actual principal-open restriction.
It is definitionally the identity on every underlying sheaf and morphism. -/
def finiteTypePrincipalRestrictionSquare :
    (finiteTypeSheavesAffineEquivalence R).functor ⋙ affinePrincipalRestriction R r ≅
      finiteTypeSheavesRestriction (principalOpen R r) ⋙
        (finiteTypeSheavesAffineEquivalence (CommRingCat.of (Localization.Away r))).functor :=
  Iso.refl _

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
