/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FiniteComplement

/-!
# Compactly supported cohomology with a finite closed complement

The examples restate the bijectivity of `H^r_c(U, j^* G) → H^r(X, G)` for `r ≥ 2`, the
exactness of `0 → H^0_c(U, j^* G) → H^0(X, G) → H^0(pointScheme X D, i^* G) → H^1_c(U, j^* G)
→ H^1(X, G) → 0`, and the positive-degree acyclicity of the finite closed part, and guard the
axioms of every public declaration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteClosedSupport

universe w w' u

namespace AglibTest.CompactSupportFiniteComplement

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (D : Set X)
  (hD : Set.range j = Dᶜ) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))
  (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pointScheme X D))]
  (G : AbelianSheaf.{u, u + 1} X)

/-- `H^r_c(U, j^* G) ≅ H^r(X, G)` for `r ≥ 2`, through the original counit. -/
example (r : ℕ) (hr : 2 ≤ r) (x : CompactSupport.H j ((inverseImage j).obj G) r) :
    Function.Bijective (CompactSupport.counitMap j G r) ∧
      CompactSupport.counitAddEquiv D hfin hclosed hsep j hD G r hr x =
        Sheaf.H.map ((etaleLowerShriekAdjunction j).counit.app G) r x :=
  ⟨CompactSupport.counitMap_bijective_of_finite_of_sepClosed D hfin hclosed hsep j hD G r hr, rfl⟩

/-- The low-degree exact sequence through the finite point scheme. -/
example :
    Function.Injective (CompactSupport.counitMap j G 0) ∧
      Function.Exact (CompactSupport.counitMap j G 0)
        (CompactSupport.pointRestriction.{w, w'} D hfin hclosed G 0) ∧
      Function.Exact (CompactSupport.pointRestriction.{w, w'} D hfin hclosed G 0)
        (CompactSupport.pointBoundary.{w, w'} D hfin hclosed G j hD 0 1 rfl) ∧
      Function.Exact (CompactSupport.pointBoundary.{w, w'} D hfin hclosed G j hD 0 1 rfl)
        (CompactSupport.counitMap j G 1) ∧
      Function.Surjective (CompactSupport.counitMap j G 1) :=
  ⟨CompactSupport.counitMap_zero_injective_of_finite D hfin hclosed j hD G,
    CompactSupport.exact_counitMap_pointRestriction D hfin hclosed G j hD 0,
    CompactSupport.exact_pointRestriction_pointBoundary D hfin hclosed G j hD 0 1 rfl,
    CompactSupport.exact_pointBoundary_counitMap D hfin hclosed G j hD 0 1 rfl,
    CompactSupport.counitMap_one_surjective_of_finite_of_sepClosed D hfin hclosed hsep j hD G⟩

/-- Positive cohomology of a finite direct image from the point scheme vanishes. -/
example (M : AbelianSheaf.{u, u + 1} (pointScheme X D)) (r : ℕ) (hr : 0 < r) :
    Subsingleton (Sheaf.H.{w} ((directImage (inclusion X D)).obj M) r) :=
  CompactSupport.subsingleton_H_directImage_inclusion_of_sepClosed D hfin hclosed hsep M r hr

end AglibTest.CompactSupportFiniteComplement

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_surjective_of_subsingleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_surjective_of_subsingleton

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_injective_of_subsingleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_injective_of_subsingleton

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_bijective_of_subsingleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_bijective_of_subsingleton

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.range_eq_compl_range_inclusion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.range_eq_compl_range_inclusion

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_directImage_inclusion_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_directImage_inclusion_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_bijective_of_finite_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_bijective_of_finite_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_one_surjective_of_finite_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_one_surjective_of_finite_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_zero_injective_of_finite' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_zero_injective_of_finite

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRestriction_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRestriction_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointBoundary_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointBoundary_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_counitMap_pointRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_counitMap_pointRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointRestriction_pointBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointRestriction_pointBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointBoundary_counitMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointBoundary_counitMap

