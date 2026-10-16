/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
/-!
# Affine-locally finite-type sheaves on an affine scheme

Finite global generating sections restrict to finite global generating
sections under every open immersion. On an affine target, quasicoherence
turns these into finite global sections. Consequently the all-affine-chart
finite-type condition on `Spec R` agrees with the actual affine
finite-module condition.

The equivalence below changes neither the underlying sheaves nor their
morphisms, over any base ring. It gives the affine category a small model
in the base ring's universe. Under noetherianity, it also identifies the two
abelian exact categories.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open ModuleCat
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable (R : CommRingCat.{u})

/-- The affine-chart finite-type quasicoherent predicate agrees with
quasicoherence and finite global sections on an affine scheme over any ring. -/
theorem affineLocallyFiniteType_spec_iff (M : (Spec R).Modules) :
    affineLocallyFiniteType (Spec R) M ↔ affineFiniteSheaf R M := by
  constructor
  · intro hM
    exact (affineFiniteSheaf R).prop_of_iso (Scheme.Modules.restrictFunctorId.app M)
      (hM R (𝟙 (Spec R)))
  · intro hM S j _
    exact affineFiniteSheaf_restrict R j hM

/-- Equality of the two actual object properties on affine module sheaves. -/
theorem affineLocallyFiniteType_spec_eq_affineFiniteSheaf : affineLocallyFiniteType (Spec R) =
  affineFiniteSheaf R := by
  funext M
  exact propext (affineLocallyFiniteType_spec_iff R M)

/-- Affine-locally finite-type sheaves on `Spec R` are equivalent to affine
quasicoherent sheaves of finite type. Both directions preserve the underlying
sheaf and all morphisms definitionally. -/
def finiteTypeSheavesAffineEquivalence : FiniteTypeSheaves (Spec R) ≌ AffineFiniteType R where
  functor :=
    { obj M :=
        let h := (affineLocallyFiniteType_spec_iff R M.obj).mp M.property
        ⟨⟨M.obj, h.1⟩, h.2⟩
      map f := ObjectProperty.homMk (ObjectProperty.homMk f.hom) }
  inverse :=
    { obj M := ⟨M.obj.obj, (affineLocallyFiniteType_spec_iff R M.obj.obj).mpr ⟨M.obj.property,
      M.property⟩⟩
      map f := ObjectProperty.homMk f.hom.hom }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by intro M; rfl

/-- The affine comparison commutes with actual sheaf inclusions. -/
theorem finiteTypeSheavesAffineEquivalence_comp_inclusion :
    (finiteTypeSheavesAffineEquivalence R).functor ⋙ affineFiniteTypeToModules R =
      finiteTypeSheavesToModules (Spec R) := rfl

/-- Affine-locally finite-type sheaves on an affine scheme are essentially
small in the base ring's universe. -/
instance finiteTypeSheavesSpec_essentiallySmall : EssentiallySmall.{u} (FiniteTypeSheaves (Spec R))
  :=
  essentiallySmall_of_fully_faithful (finiteTypeSheavesAffineEquivalence R).functor

/-- The affine equivalence identifies affine-locally finite-type sheaves
with finite modules over the base ring. -/
def finiteTypeSheavesSpecModuleEquivalence : FiniteTypeSheaves (Spec R) ≌ FiniteModule.{u, u} R :=
  (finiteTypeSheavesAffineEquivalence R).trans (affineFiniteTypeModuleEquivalence R)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
