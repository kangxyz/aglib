/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.CurveRoots

/-!
# Compactly supported cohomology of roots of unity on an affine curve

The examples restate, for a smooth proper geometrically connected curve over an algebraically
closed field and the complement `U` of a finite nonempty set of closed points, that
`H^2_c(U, μ_n) → H^2(X, μ_n)` is bijective, that `H^r_c(U, μ_n) = 0` for `r ≥ 3`, and that
`H^0_c(U, μ_n) = 0`, together with the general finite-complement statements, and guard the
axioms of every public declaration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.OverField GroupCohomology.Kummer.Coefficients

universe w u

namespace AglibTest.CompactSupportCurveRoots

attribute [local instance] hasSheafifyLarge

section General

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(X, ⊤))) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] (D : Set X)
  (hD : Set.range j = Dᶜ) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))
  (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))

/-- The roots map is the coefficient isomorphism followed by the original counit map, and it
is bijective in degree at least two. -/
example (r : ℕ) (hr : 2 ≤ r) :
    CompactSupport.rootsMap.{w} j n hn hinv r =
        (CompactSupport.counitMap j (mu X n) r).comp
          (CompactSupport.H.map j
            (GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso j n hn hinv).inv r) ∧
      Function.Bijective (CompactSupport.rootsMap.{w} j n hn hinv r) :=
  ⟨CompactSupport.rootsMap_eq_comp j n hn hinv r,
    CompactSupport.rootsMap_bijective_of_sepClosed j n hn hinv D hD hfin hclosed hsep r hr⟩

/-- The roots map is injective in degree zero. -/
example : Function.Injective (CompactSupport.rootsMap.{w} j n hn hinv 0) :=
  CompactSupport.rootsMap_zero_injective j n hn hinv D hD hfin hclosed

end General

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hDne : D.Nonempty) (hfin : D.Finite)
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hunit : IsUnit (n : k)) [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- Over an algebraically closed field, `H^2_c(U, μ_n) ≅ H^2(X, μ_n)` (SGA 4 XVIII (1.1.3.1)). -/
example (hn : 0 < n) :
    Function.Bijective (CompactSupport.rootsMap.{w} j n hn
      (CompactSupport.isUnit_natCast_globalSections X hunit) 2) :=
  CompactSupport.rootsMap_bijective_of_curve X hX D hfin hclosed j hD n hn _ 2 le_rfl

/-- `H^r_c(U, μ_n) = 0` for `r ≥ 3`. -/
example (r : ℕ) (hr : 3 ≤ r) : Subsingleton (CompactSupport.H.{w} j (mu U n) r) :=
  CompactSupport.subsingleton_H_roots_of_curve X hX D hfin hclosed j hD n hunit r hr

/-- `H^0_c(U, μ_n) = 0` for a nonempty finite set of closed points. -/
example : Subsingleton (CompactSupport.H.{w} j (mu U n) 0) :=
  CompactSupport.subsingleton_H_roots_zero_of_curve X hX D hfin hclosed j hD n hDne hunit

end Curve

end AglibTest.CompactSupportCurveRoots

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsExtensionMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsExtensionMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_eq_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_eq_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_zero_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_zero_injective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_roots_zero_of_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_roots_zero_of_injective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_bijective_of_sepClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_bijective_of_sepClosed

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.isUnit_natCast_globalSections' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.isUnit_natCast_globalSections

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_bijective_of_curve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_bijective_of_curve

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_roots_of_curve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_roots_of_curve

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_roots_zero_of_curve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.subsingleton_H_roots_zero_of_curve

