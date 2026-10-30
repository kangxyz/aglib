/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CurveCohomology.Proper

/-!
# The cohomology of `μ_n` and `ℤ/n` on a smooth proper curve

The examples restate, for a smooth proper geometrically connected curve over an algebraically
closed field and `n` invertible in the field, the identifications `H^0(X, μ_n) ≅ μ_n(k)`,
`H^1(X, μ_n) ≅ Pic(X)[n]`, `H^2(X, μ_n) ≅ ℤ/n`, `H^q(X, μ_n) = 0` for `q ≥ 3`, and the same with
`ℤ/n` coefficients, and guard the axioms of every public declaration.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField GroupCohomology.Kummer.Coefficients

universe w u

namespace AglibTest.CurveCohomologyProper

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- The table of `H^q(X, μ_n)` (Stacks, Tag 03RQ). -/
example : Nonempty (Sheaf.H.{w} (mu X.left n) 0 ≃+ Additive (rootsOfUnity n k)) ∧
    Nonempty (Sheaf.H.{w} (mu X.left n) 1 ≃+ Torsion.picardTorsion X.left n) ∧
    Nonempty (Sheaf.H.{w} (mu X.left n) 2 ≃+ ZMod n) ∧
    ∀ q, 2 < q → Subsingleton (Sheaf.H.{w} (mu X.left n) q) := by
  have := Curve.curveProperties_locallyOfFiniteType hX
  have := hX.proper
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ⟨⟨Curves.rootsZeroAddEquiv hX n⟩, ⟨Curves.rootsOneAddEquiv hX n hn hinv⟩,
    ⟨Curves.traceAddEquiv hX n hn hunit hinv⟩, fun q hq =>
      Curves.roots_subsingleton_H_of_curve k X.left X.hom hX.topologicalKrullDim_eq_one.le n hn
        hunit hinv q hq⟩

/-- The table of `H^q(X, ℤ/n)` through `ℤ/n ≅ μ_n`. -/
example :
    Nonempty (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 0 ≃+
      Additive (rootsOfUnity n k)) ∧
    Nonempty (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 1 ≃+
      Torsion.picardTorsion X.left n) ∧
    Nonempty (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 2 ≃+
      ZMod n) ∧
    ∀ q, 2 < q →
      Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) q) :=
  ⟨⟨Curves.constantZeroAddEquiv hX n hn hunit⟩, ⟨Curves.constantOneAddEquiv hX n hn hunit hinv⟩,
    ⟨Curves.constantTwoAddEquiv hX n hn hunit hinv⟩,
    fun q hq => Curves.constant_subsingleton_H_of_curve hX n hn hunit hinv q hq⟩

/-- The constant coefficient comparison is the map induced by `ℤ/n ≅ μ_n`. -/
example (q : ℕ)
    (a : Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) q) :
    Curves.constantRootsAddEquiv (X := X) n hn hunit q a =
      Sheaf.H.map (Curves.constantRootIso (X := X) n hn hunit).hom q a :=
  Curves.constantRootsAddEquiv_apply n hn hunit q a

/-- The constants of the curve. -/
example (a : k) : Curves.constantsRingEquiv hX a = Scheme.constants X a :=
  Curves.constantsRingEquiv_apply hX a

/-- The proper H1 equivalence has the original Kummer Picard map as its underlying map. -/
example (x : Sheaf.H.{w} (mu X.left n) 1) :
    (Curves.rootsOneAddEquiv hX n hn hinv x).val = Kummer.rootsPicardMap X.left n x :=
  DFunLike.congr_fun (Curves.rootsOneAddEquiv_subtype hX n hn hinv) x

end AglibTest.CurveCohomologyProper

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantsRingEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantsRingEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantsRingEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantsRingEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsZeroAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsZeroAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsOneAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsOneAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantRootIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantRootIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantRootsAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantRootsAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantRootsAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantRootsAddEquiv_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantZeroAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantZeroAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantOneAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantOneAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantTwoAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constantTwoAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constant_subsingleton_H_of_curve' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.constant_subsingleton_H_of_curve

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsOneAddEquiv_subtype' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsOneAddEquiv_subtype
