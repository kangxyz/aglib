/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.CohomologyVanishing

/-! Actual prime constant tests for the original finite-local-system cohomology. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r w

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

example (X : Scheme.{u}) [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (R : Type r) [CommRing R] [Finite R]
    [(forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).Full]
    (n : ℕ) (hn : 0 < n) (q : ℕ)
    (hconstant : ∀ (p : ℕ), p.Prime → p ∣ n → ∀ Y : Scheme.FiniteEtale X,
      let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.obj.left) := hasExtStandard Y.obj.left
      Subsingleton (Sheaf.H.{u + 2} (primeFieldSheaf Y.obj.left p) q))
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) (hkill : n • 𝟙 F = 0) :
    Subsingleton ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj F) :=
  moduleSheaf_cohomology_subsingleton_of_constant_prime_tests X R n hn q hconstant F hF hkill

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.constantCohomology_subsingleton_of_prime_field' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.constantCohomology_subsingleton_of_prime_field

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.moduleSheaf_cohomology_subsingleton_of_pGroup_trivialization' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.moduleSheaf_cohomology_subsingleton_of_pGroup_trivialization

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.moduleSheaf_cohomology_subsingleton_of_galois_prime_trivialization' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.moduleSheaf_cohomology_subsingleton_of_galois_prime_trivialization

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.moduleSheaf_cohomology_subsingleton_of_constant_prime_tests' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.moduleSheaf_cohomology_subsingleton_of_constant_prime_tests
