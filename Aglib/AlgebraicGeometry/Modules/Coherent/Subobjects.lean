/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic

/-!
# Quasicoherent subobjects of coherent sheaves

Over a Noetherian affine ring, a quasicoherent subobject of a finite-type quasicoherent sheaf is
finite type. Its locally Noetherian scheme form retains the quasicoherence hypothesis on the
subobject.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/Subobjects.lean`.
SHA-256: `b0d509827c73ec232ff7a4dc53b1582b58678b4ccbc5d0756540e1e8cf153f21`.
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
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- On a noetherian affine, a quasicoherent sheaf embedded in a coherent
sheaf is finite. Global sections preserve the monomorphism, and a submodule
of a finite module over a noetherian ring is finite. -/
theorem affineFiniteSheaf_of_mono (R : CommRingCat.{u}) [IsNoetherianRing R]
    {M N : (Spec R).Modules} (f : M ⟶ N) [Mono f] [M.IsQuasicoherent]
    (hN : affineFiniteSheaf R N) : affineFiniteSheaf R M := by
  have : Module.Finite R (moduleSpecΓFunctor.obj N) := hN.2
  have : (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint
  refine ⟨inferInstance, ?_⟩
  exact Module.Finite.of_injective (moduleSpecΓFunctor.map f).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- Every quasicoherent subobject of an actual coherent sheaf on a locally
noetherian scheme is coherent. This makes no false assertion about arbitrary
subobjects in the category of all module sheaves. -/
theorem affineLocallyFiniteType_of_quasicoherent_mono {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} (f : M ⟶ N) [Mono f] [M.IsQuasicoherent]
    (hN : affineLocallyFiniteType X N) : affineLocallyFiniteType X M := by
  intro R j _
  let : IsNoetherianRing R := noetherian_affineChart R j
  exact affineFiniteSheaf_of_mono R ((Scheme.Modules.restrictFunctor j).map f) (hN R j)

end AlgebraicGeometry.Scheme.Modules.Coherent
