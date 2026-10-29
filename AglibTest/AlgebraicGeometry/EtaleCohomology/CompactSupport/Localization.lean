/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Localization

/-!
# The open-closed long exact sequence of compactly supported cohomology

The examples check that the connecting map is the original one of the localization sequence,
restate the exactness of `H^r_c(U, j^* G) → H^r(X, G) → H^r(X, i_* i^* G) → H^{r+1}_c(U, j^* G)`
and the degree-zero injectivity, and guard the axioms of every public declaration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleCohomology

universe w u

namespace AglibTest.CompactSupportLocalization

attribute [local instance] hasSheafifyLarge

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i] (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (G : AbelianSheaf.{u, u + 1} X)

/-- The connecting map is the original connecting map of the localization sequence. -/
example (n : ℕ) :
    CompactSupport.localizationδ j i hcomp G n (n + 1) rfl =
      Sheaf.H.δ (abelianLocalization_shortExact j i hcomp G) n (n + 1) rfl :=
  rfl

/-- The long exact sequence is exact at its three kinds of terms. -/
example (r : ℕ) :
    Function.Exact (CompactSupport.counitMap j G r)
        (Sheaf.H.map ((inverseImageAdjunction i).unit.app G) r) ∧
      Function.Exact (Sheaf.H.map ((inverseImageAdjunction i).unit.app G) r)
        (CompactSupport.localizationδ j i hcomp G r (r + 1) rfl) ∧
      Function.Exact (CompactSupport.localizationδ j i hcomp G r (r + 1) rfl)
        (CompactSupport.counitMap j G (r + 1)) :=
  ⟨CompactSupport.exact_counitMap_unitMap j i hcomp G r,
    CompactSupport.exact_unitMap_localizationδ j i hcomp G r (r + 1) rfl,
    CompactSupport.exact_localizationδ_counitMap j i hcomp G r (r + 1) rfl⟩

/-- The composable-arrows form of the long exact sequence. -/
example (n : ℕ) : (CompactSupport.localizationSequence j i hcomp G n (n + 1) rfl).Exact :=
  CompactSupport.localizationSequence_exact j i hcomp G n (n + 1) rfl

/-- The counit map is injective in degree zero. -/
example : Function.Injective (CompactSupport.counitMap j G 0) :=
  CompactSupport.counitMap_zero_injective j i hcomp G

end AglibTest.CompactSupportLocalization

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.localizationδ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.localizationδ

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.localizationSequence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.localizationSequence

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.localizationSequence_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.localizationSequence_exact

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_counitMap_unitMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_counitMap_unitMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_unitMap_localizationδ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_unitMap_localizationδ

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_localizationδ_counitMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_localizationδ_counitMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_zero_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_zero_injective

