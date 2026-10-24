/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstantTorsionCurveH1
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantUnderlyingCohomology

/-!
# Finite original H1 of actual constant torsion module sheaves

The native scalar-linear constant-underlying comparison transfers the original
constant-coefficient theorem to actual `ModuleCat`-valued constant sheaves.
The original coefficient-ring action and independent universes are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness

universe u e l

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {k : Type u} [Field k] [IsSepClosed k] (X : FScheme k) (hX : Properties X)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X.left)]
  [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}]
  (Λ : Type l) [CommRing Λ] [IsNoetherianRing Λ]

include hX

/-- Any positive additive annihilator gives finite original H1 of the actual
constant module sheaf, including its characteristic-primary coefficients. -/
theorem constantModuleSheaf_h1_finite_of_pos_nsmul
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, n • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology Λ 1).obj
      ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  (ModuleCat.Sheaf.finite_cohomology_constant_iff X.left.smallEtaleTopology Λ 1 M).mpr
    (constantModule_h1_finite_of_pos_nsmul X hX Λ n hn M hM)

/-- A finite additively torsion module has finite original H1 when regarded as
an actual constant module sheaf on the smooth proper geometric curve. -/
theorem constantModuleSheaf_h1_finite_of_isAddTorsion
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] (hM : IsAddTorsion M) :
    Module.Finite Λ ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology Λ 1).obj
      ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  (ModuleCat.Sheaf.finite_cohomology_constant_iff X.left.smallEtaleTopology Λ 1 M).mpr
    (constantModule_h1_finite_of_isAddTorsion X hX Λ M hM)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness
