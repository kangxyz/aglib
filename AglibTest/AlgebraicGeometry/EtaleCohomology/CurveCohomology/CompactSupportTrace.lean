/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CurveCohomology.CompactSupportTrace

/-!
# The trace on compactly supported cohomology of an open curve

The examples restate, for the complement `U` of a finite set of closed points of a smooth proper
geometrically connected curve over an algebraically closed field and `n` invertible in the field,
the trace `H^2_c(U, μ_n) ≃+ ℤ/n` and its value through `H^2_c(U, μ_n) ≅ H^2(X, μ_n)`, and guard
the axioms of every public declaration.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.OverField GroupCohomology.Kummer.Coefficients

universe w u

namespace AglibTest.CurveCohomologyCompactSupportTrace

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- The trace `H^2_c(U, μ_n) ≃+ ℤ/n` is the trace of `X` after `H^2_c(U, μ_n) ≅ H^2(X, μ_n)`. -/
example (x : CompactSupport.H.{w} j (mu U n) 2) :
    Curves.compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv x =
      Curves.traceAddEquiv hX n hn hunit hinv (CompactSupport.rootsMap j n hn hinv 2 x) :=
  Curves.compactSupportTraceAddEquiv_apply X hX D hfin hclosed j hD n hn hunit hinv x

/-- In particular `H^2_c(U, μ_n)` is cyclic of order `n`. -/
example : Nonempty (CompactSupport.H.{w} j (mu U n) 2 ≃+ ZMod n) :=
  ⟨Curves.compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv⟩

end AglibTest.CurveCohomologyCompactSupportTrace

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv_apply
