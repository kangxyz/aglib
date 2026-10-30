/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CurveCohomology.Complement

/-!
# The cohomology of `μ_n` on an open subscheme of a curve

The examples restate the exact sequence `0 → Γ(Y, 𝒪_Y)^×/n → H^1(Y, μ_n) → Pic(Y)[n] → 0` on
every scheme, and, for the complement `U = X − D` of a nonempty set of closed points of a smooth
proper geometrically connected curve over an algebraically closed field, that `H^q(U, μ_n) = 0`
for `q ≥ 2`; and guard the axioms of every public declaration.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField GroupCohomology.Kummer.Coefficients

universe w u

namespace AglibTest.CurveCohomologyComplement

attribute [local instance] hasSheafifyLarge

section General

variable (Y : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)] (n : ℕ) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(Y, ⊤)))

/-- The exact sequence `0 → Γ(Y, 𝒪_Y)^×/n → H^1(Y, μ_n) → Pic(Y)[n] → 0`. -/
example : Function.Injective (Kummer.unitsQuotientBoundary.{u, w} Y n hn hinv) ∧
    Function.Exact (Kummer.unitsQuotientBoundary.{u, w} Y n hn hinv)
      (Kummer.rootsPicardMap.{u, w} Y n) ∧
    (Kummer.rootsPicardMap.{u, w} Y n).range = Torsion.picardTorsion Y n :=
  ⟨Kummer.unitsQuotientBoundary_injective Y n hn hinv,
    Kummer.exact_unitsQuotientBoundary_rootsPicardMap Y n hn hinv,
    Kummer.range_rootsPicardMap Y n hn hinv⟩

/-- The units boundary vanishes exactly on `n`-th powers. -/
example (a : Additive Γ(Y, ⊤)ˣ) :
    Kummer.unitsBoundary.{u, w} Y n hn hinv a = 0 ↔ ∃ b, n • b = a :=
  Kummer.unitsBoundary_eq_zero_iff Y n hn hinv a

end General

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] [HasExt.{w} (AbelianSheaf.{u, u + 1} U)]
  (n : ℕ) (hunit : IsUnit (n : k))

/-- `H^q(X − D, μ_n) = 0` for `q ≥ 2` and a nonempty set `D` of closed points. -/
example (D : Set X.left) (hDne : D.Nonempty) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
    (hD : Set.range j = Dᶜ) (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H.{w} (mu U n) q) :=
  Curves.roots_subsingleton_H_of_range_eq_compl hX j D hDne hclosed hD n hunit q hq

/-- The same for an open immersion whose image misses a closed point, in degree two. -/
example (hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j) :
    Subsingleton (Sheaf.H.{w} (mu U n) 2) :=
  Curves.roots_subsingleton_H_two_of_isOpenImmersion hX j hx n hunit

end Curve

end AglibTest.CurveCohomologyComplement











/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.roots_subsingleton_H_two_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.roots_subsingleton_H_two_of_isOpenImmersion

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.roots_subsingleton_H_of_isOpenImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.roots_subsingleton_H_of_isOpenImmersion

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.roots_subsingleton_H_of_range_eq_compl' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.roots_subsingleton_H_of_range_eq_compl
