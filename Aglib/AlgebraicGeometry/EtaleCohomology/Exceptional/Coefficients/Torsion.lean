/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Torsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.CategoryTheory.Sites.Torsion.Sheaf

/-!
# Genuine module coefficients and internal torsion

The torsion condition is the existing local-annihilator sheaf condition.
It is not replaced by a global annihilator or torsion of every section on
an arbitrary object. A positive annihilator of the coefficient ring's unit
is sufficient for every native module sheaf to satisfy the local condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules

attribute [local instance] CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard


variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The existing internal torsion property of the actual underlying module sheaf. -/
def moduleIsTorsion (M : ModuleSheaf X Λ) : Prop :=
  ModuleCat.Sheaf.ConstantRing.moduleIsTorsion (Scheme.smallEtaleTopology X) Λ M

/-- Internal torsion is retained by an actual native module isomorphism. -/
theorem moduleIsTorsion_of_iso {M N : ModuleSheaf X Λ} (e : M ≅ N)
    (hN : moduleIsTorsion X Λ N) : moduleIsTorsion X Λ M :=
  ModuleCat.Sheaf.ConstantRing.moduleIsTorsion_of_iso (Scheme.smallEtaleTopology X) Λ e hN

/-- A positive annihilator of the scalar unit annihilates every original module-valued section. -/
theorem moduleValuedUnderlying_isTorsion_of_nsmul_one_eq_zero
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) (M : ModuleValuedSheaf X Λ) :
    Sheaf.IsTorsion
      ((sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M) :=
  ModuleCat.Sheaf.ConstantRing.moduleValuedUnderlying_isTorsion_of_nsmul_one_eq_zero
    (Scheme.smallEtaleTopology X) Λ N hN hΛ M

/-- Every genuine native module sheaf over a torsion ring is internally torsion. -/
theorem moduleIsTorsion_of_nsmul_one_eq_zero
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) (M : ModuleSheaf X Λ) :
    moduleIsTorsion X Λ M :=
  ModuleCat.Sheaf.ConstantRing.moduleIsTorsion_of_nsmul_one_eq_zero
    (Scheme.smallEtaleTopology X) Λ N hN hΛ M

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
