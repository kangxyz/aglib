/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstantPrimaryModules
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantUnderlyingCohomology

/-!
# Finite original cohomology of actual constant module sheaves

These conclusions use the native constant `ModuleCat`-valued sheaf and its
original underlying-abelian cohomology, with the actual coefficient-ring action.
The scalar-compatible native underlying comparison transfers the constant
abelian-coefficient results without any finite-underlying-group assumption.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e l

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {k : Type u} [Field k] [IsSepClosed k] (Y : FScheme k) [IsProper Y.hom]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y.left)]
  [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  (Λ : Type l) [CommRing Λ]

/-- Prime-killed finite modules have finite original cohomology when regarded as
actual native constant module sheaves. The coefficient ring need not be Noetherian. -/
theorem constantModuleSheaf_cohomology_finite_of_prime_nsmul
    (q : ℕ) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, p • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.cohomology Y.left.smallEtaleTopology Λ q).obj
      ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  (ModuleCat.Sheaf.finite_cohomology_constant_iff Y.left.smallEtaleTopology Λ q M).mpr
    (constantModule_cohomology_finite_of_prime_nsmul Y p Λ q M hM)

/-- Every positive characteristic-primary exponent gives finite original
cohomology of actual constant module sheaves over the original Noetherian ring. -/
theorem constantModuleSheaf_cohomology_finite_of_prime_power [IsNoetherianRing Λ]
    (q n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hM : ∀ x : M, (p ^ n) • x = 0) :
    Module.Finite Λ ((ModuleCat.Sheaf.cohomology Y.left.smallEtaleTopology Λ q).obj
      ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  (ModuleCat.Sheaf.finite_cohomology_constant_iff Y.left.smallEtaleTopology Λ q M).mpr
    (constantModule_cohomology_finite_of_prime_power Y p Λ q n hn M hM)

end AlgebraicGeometry.Scheme.EtaleCohomology
