/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.PointRemoval

/-!
# Removing finitely many points from an open subscheme

The examples restate the short exact sequence `0 → j_{V!}(F|_V) → j_{U!} F → i_* i^* j_{U!} F
→ 0`, the bijectivity of `H^r_c(V, F|_V) → H^r_c(U, F)` for `r ≥ 2`, the vanishing of the third
term in positive degree and the low-degree exact sequence, and guard the axioms of every public
declaration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Curves.FiniteClosedSupport

universe w w' u

namespace AglibTest.CompactSupportPointRemoval

attribute [local instance] hasSheafifyLarge

variable {V U X : Scheme.{u}} (jV : V ⟶ U) [IsOpenImmersion jV] (jU : U ⟶ X)
  [IsOpenImmersion jU] (F : AbelianSheaf.{u, u + 1} U) (D : Set X)
  (hD : Set.range (jV ≫ jU) = Dᶜ) (hfin : D.Finite)
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))
  (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pointScheme X D))]

/-- The point-removal sequence is short exact, with the original arrows. -/
example :
    (CompactSupport.pointRemovalShortComplex jV jU F D hD hfin hclosed).ShortExact ∧
      (CompactSupport.pointRemovalShortComplex jV jU F D hD hfin hclosed).g =
        (inverseImageAdjunction (inclusion X D)).unit.app ((etaleLowerShriek jU).obj F) ∧
      CompactSupport.extensionMap jV jU F =
        (etaleLowerShriek (jV ≫ jU)).map (CompactSupport.restrictionExtensionIso jV jU F).inv ≫
          (etaleLowerShriekAdjunction (jV ≫ jU)).counit.app ((etaleLowerShriek jU).obj F) :=
  ⟨CompactSupport.pointRemoval_shortExact jV jU F D hD hfin hclosed, rfl, rfl⟩

/-- `H^r_c(V, F|_V) ≅ H^r_c(U, F)` for `r ≥ 2`. -/
example (r : ℕ) (hr : 2 ≤ r) :
    Function.Bijective (CompactSupport.extensionCohomologyMap.{w} jV jU F r) :=
  CompactSupport.extensionCohomologyMap_bijective_of_sepClosed jV jU F D hD hfin hclosed hsep r hr

/-- The third term is acyclic in positive degree. -/
example (r : ℕ) (hr : 0 < r) :
    Subsingleton (Sheaf.H.{w} ((directImage (inclusion X D)).obj
      ((inverseImage (inclusion X D)).obj ((etaleLowerShriek jU).obj F))) r) :=
  CompactSupport.subsingleton_H_pointRemoval_third_of_sepClosed jU F D hfin hclosed hsep r hr

/-- The low-degree exact sequence through the finite point scheme. -/
example :
    Function.Injective (CompactSupport.extensionCohomologyMap.{w} jV jU F 0) ∧
      Function.Exact (CompactSupport.extensionCohomologyMap.{w} jV jU F 0)
        (CompactSupport.pointRestriction.{w, w'} D hfin hclosed ((etaleLowerShriek jU).obj F) 0) ∧
      Function.Exact
        (CompactSupport.pointRestriction.{w, w'} D hfin hclosed ((etaleLowerShriek jU).obj F) 0)
        (CompactSupport.pointRemovalBoundary.{w, w'} jV jU F D hD hfin hclosed 0 1 rfl) ∧
      Function.Exact (CompactSupport.pointRemovalBoundary.{w, w'} jV jU F D hD hfin hclosed 0 1 rfl)
        (CompactSupport.extensionCohomologyMap.{w} jV jU F 1) ∧
      Function.Surjective (CompactSupport.extensionCohomologyMap.{w} jV jU F 1) :=
  ⟨CompactSupport.extensionCohomologyMap_zero_injective jV jU F D hD hfin hclosed,
    CompactSupport.exact_extensionCohomologyMap_pointRestriction jV jU F D hD hfin hclosed 0,
    CompactSupport.exact_pointRestriction_pointRemovalBoundary jV jU F D hD hfin hclosed 0 1 rfl,
    CompactSupport.exact_pointRemovalBoundary_extensionCohomologyMap jV jU F D hD hfin hclosed
      0 1 rfl,
    CompactSupport.extensionCohomologyMap_surjective_of_sepClosed jV jU F D hD hfin hclosed hsep 1 one_pos⟩

end AglibTest.CompactSupportPointRemoval

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.restrictionExtensionIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.restrictionExtensionIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalShortComplex' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalShortComplex

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemoval_shortExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemoval_shortExact

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalδ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalδ

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalSequence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalSequence

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalSequence_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalSequence_exact

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_extensionCohomologyMap_unitMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_extensionCohomologyMap_unitMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_unitMap_pointRemovalδ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_unitMap_pointRemovalδ

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointRemovalδ_extensionCohomologyMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointRemovalδ_extensionCohomologyMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_zero_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_zero_injective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_pointRemoval_third_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_pointRemoval_third_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_surjective_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_surjective_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_injective_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_injective_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_bijective_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyMap_bijective_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.extensionCohomologyAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalBoundary_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.pointRemovalBoundary_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_extensionCohomologyMap_pointRestriction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_extensionCohomologyMap_pointRestriction

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointRestriction_pointRemovalBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointRestriction_pointRemovalBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointRemovalBoundary_extensionCohomologyMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_pointRemovalBoundary_extensionCohomologyMap

