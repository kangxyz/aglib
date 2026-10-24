/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant

/-! # Constructible finite-type module coefficients

Constructibility uses the existing actual affine-local finite partitions by
constructible locally closed subschemes. Each module restriction is finite-type
locally constant over the original coefficient ring. In particular, the
definition permits finite modules with infinite underlying additive groups.
Over a finite ring its original underlying abelian coefficient is constructible.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- An existing actual locally closed partition with finite-type locally
constant module restriction on each original stratum. -/
structure ConstructiblePartition {X : Scheme.{u}} (F : ModuleSheaf R X)
    extends FiniteLocallyClosedPartition X where
  /-- Finite-type local constancy of the actual module inverse image. -/
  locally_constant : ∀ i,
    IsFiniteTypeLocallyConstant ((moduleInverseImage R (inclusion i)).obj F)

/-- A module isomorphism transports the same strata and immersions. -/
def ConstructiblePartition.ofIso {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (t : ConstructiblePartition F) (e : F ≅ G) : ConstructiblePartition G where
  toFiniteLocallyClosedPartition := t.toFiniteLocallyClosedPartition
  locally_constant i :=
    (isFiniteTypeLocallyConstant_iff_of_iso
      ((moduleInverseImage R (t.inclusion i)).mapIso e)).mp (t.locally_constant i)

/-- Finite-type local constancy yields the identity partition. -/
def ConstructiblePartition.ofFiniteTypeLocallyConstant {X : Scheme.{u}}
    {F : ModuleSheaf R X} (hF : IsFiniteTypeLocallyConstant F) :
    ConstructiblePartition F where
  toFiniteLocallyClosedPartition := FiniteLocallyClosedPartition.singleton X
  locally_constant _ := isFiniteTypeLocallyConstant_pullback (𝟙 X) hF

/-- Every affine open has an actual finite locally closed partition with
finite-type locally constant module restrictions. -/
def IsConstructible {X : Scheme.{u}} (F : ModuleSheaf R X) : Prop :=
  ∀ U : X.affineOpens,
    Nonempty (ConstructiblePartition ((moduleInverseImage R U.1.ι).obj F))

/-- Constructibility is invariant under actual module coefficient isomorphisms. -/
theorem isConstructible_iff_of_iso {X : Scheme.{u}} {F G : ModuleSheaf R X} (e : F ≅ G) :
    IsConstructible F ↔ IsConstructible G := by
  constructor
  · intro h U
    obtain ⟨t⟩ := h U
    exact ⟨t.ofIso ((moduleInverseImage R U.1.ι).mapIso e)⟩
  · intro h U
    obtain ⟨t⟩ := h U
    exact ⟨t.ofIso ((moduleInverseImage R U.1.ι).mapIso e.symm)⟩

/-- Finite-type local constancy implies affine-local module constructibility. -/
theorem isConstructible_of_isFiniteTypeLocallyConstant {X : Scheme.{u}}
    {F : ModuleSheaf R X} (hF : IsFiniteTypeLocallyConstant F) : IsConstructible F := by
  intro U
  exact ⟨ConstructiblePartition.ofFiniteTypeLocallyConstant
    (isFiniteTypeLocallyConstant_pullback U.1.ι hF)⟩

/-- Finite-type constant modules are constructible over an arbitrary coefficient ring. -/
theorem isConstructible_constant (X : Scheme.{u}) (M : ModuleCat.{u + 1} R)
    [Module.Finite R M] :
    IsConstructible ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :=
  isConstructible_of_isFiniteTypeLocallyConstant (isFiniteTypeLocallyConstant_constant X M)

/-- Over a finite coefficient ring, forgetting scalars retains the same
actual finite locally closed partition. -/
def ConstructiblePartition.underlying [Finite R] {X : Scheme.{u}} {F : ModuleSheaf R X}
    (t : ConstructiblePartition F) :
    Constructible.ConstructiblePartition ((moduleUnderlying R X).obj F) where
  toFiniteLocallyClosedPartition := t.toFiniteLocallyClosedPartition
  locally_constant i :=
    (isFiniteLocallyConstant_iff_of_iso
      ((moduleInverseImageUnderlyingIso R (t.inclusion i)).app F)).mp
        (isFiniteLocallyConstant_underlying (t.locally_constant i))

/-- Finite-ring module constructibility implies the original abelian predicate,
through the original inverse-image maps on each affine open and stratum. -/
theorem isConstructible_underlying [Finite R] {X : Scheme.{u}} {F : ModuleSheaf R X}
    (hF : IsConstructible F) : Constructible.IsConstructible ((moduleUnderlying R X).obj F) := by
  intro U
  obtain ⟨t⟩ := hF U
  exact ⟨Constructible.ConstructiblePartition.ofIso t.underlying
    ((moduleInverseImageUnderlyingIso R U.1.ι).app F)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
