/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Torsion.Derived
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Torsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage

/-!
# The actual torsion-cohomology range

Torsion is imposed on the original native homology module sheaves, using
internal local annihilators. The bounded-below range does not require a
common annihilator. A positive annihilator of the ring's unit implies this
property for every object of the whole native derived category, without
invertibility on the base or a Noetherian coefficient hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

/-- The original supplied derived model at the identical generic constant-ring module category. -/
local instance nativeConstantRingModuleSheafHasDerivedCategory :
    HasDerivedCategory.{w}
      (ModuleCat.Sheaf.ConstantRing.ModuleSheaf.{u + 1, u, u + 1, u + 1}
        (Scheme.smallEtaleTopology X) Λ) :=
  inferInstanceAs (HasDerivedCategory.{w} (ModuleSheaf X Λ))

/-- Internal torsion of every native homology module sheaf in the original derived category. -/
def moduleTorsionCohomology : ObjectProperty (DerivedCategory (ModuleSheaf X Λ)) :=
  ModuleCat.Sheaf.ConstantRing.moduleTorsionCohomology.{
    u + 1, u, u + 1, u + 1, w}
    (Scheme.smallEtaleTopology X) Λ

/-- The declared bounded-below torsion range uses the same original homology objects. -/
def moduleTorsionCohomologyPlus : ObjectProperty (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  ModuleCat.Sheaf.ConstantRing.moduleTorsionCohomologyPlus.{
    u + 1, u, u + 1, u + 1, w}
    (Scheme.smallEtaleTopology X) Λ

/-- The native torsion range is invariant under the original derived isomorphisms. -/
theorem moduleTorsionCohomology_of_iso
    {K L : DerivedCategory (ModuleSheaf X Λ)} (e : K ≅ L)
    (hL : moduleTorsionCohomology X Λ L) : moduleTorsionCohomology X Λ K :=
  ModuleCat.Sheaf.ConstantRing.moduleTorsionCohomology_of_iso.{
    u + 1, u, u + 1, u + 1, w}
    (Scheme.smallEtaleTopology X) Λ e hL

/-- A torsion ring places every native derived object in the actual torsion-cohomology range. -/
theorem moduleTorsionCohomology_of_nsmul_one_eq_zero
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
    (K : DerivedCategory (ModuleSheaf X Λ)) : moduleTorsionCohomology X Λ K :=
  ModuleCat.Sheaf.ConstantRing.moduleTorsionCohomology_of_nsmul_one_eq_zero.{
    u + 1, u, u + 1, u + 1, w}
    (Scheme.smallEtaleTopology X) Λ N hN hΛ K

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
