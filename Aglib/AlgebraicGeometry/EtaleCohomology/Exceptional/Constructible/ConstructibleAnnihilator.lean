/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.PrimeConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.PositiveAnnihilator

/-! # Original positively annihilated constructible compactified images

The global prime-killed producer supplies every test in the general
positive-annihilator induction. The source coefficient and all higher-image
maps are unchanged. Only the coefficient has a positive annihilator; the
ring is not assumed finite or of positive characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Actual compactified higher images of any positively annihilated
constructible module are constructible over the original Noetherian ring. -/
theorem moduleCompactificationHigherImage_annihilated_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    (n : ℕ) (hn : 0 < n)
    (F : ModuleValuedSheaf X Λ) (hF : Constructible.Modules.IsConstructible F)
    (hkill : n • 𝟙 F = 0) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((moduleCompactificationHigherDirectImage C Λ q).obj
          ((moduleSheafEquivalence X Λ).functor.obj F))) := by
  let : HasDerivedCategory.{u + 2} (ModuleSheaf C.Xbar Λ) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (ModuleSheaf S Λ) := HasDerivedCategory.standard _
  apply moduleCompactificationHigherImage_isConstructible_of_prime_tests
    C Λ n hn ?_ F hF hkill q
  intro p hp _ E hE hkillE j
  let : Fact p.Prime := ⟨hp⟩
  exact moduleCompactificationHigherImage_primeKilled_isConstructible
    f Λ p E hE hkillE C j

end AlgebraicGeometry.Scheme.EtaleCohomology
