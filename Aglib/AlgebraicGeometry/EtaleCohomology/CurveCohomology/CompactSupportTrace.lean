/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CurveCohomology.Trace
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.CurveRoots

/-!
# The trace on compactly supported cohomology of an open curve

Let `k` be an algebraically closed field, `X` a smooth proper geometrically connected curve over
`k` (`Curve.Properties X`), `D` a finite set of closed points of `X`, `j : U ⟶ X` the open
immersion of `U = X − D` (`Set.range j = Dᶜ`) and `n > 0` invertible in `k`.
`compactSupportTraceAddEquiv` is the trace `H^2_c(U, μ_n) ≃+ ℤ/n` (Milne, *Lectures on Étale
Cohomology* v2.21, Prop. 14.5, p. 92; SGA 4, Exp. XVIII, (1.1.3.1)–(1.1.3.3)): the isomorphism
`H^2_c(U, μ_n) → H^2(X, μ_n)` induced by `j_! μ_{n,U} ⟶ μ_{n,X}`
(`CompactSupport.rootsMap_bijective_of_curve`), followed by the trace `H^2(X, μ_n) ≃+ ℤ/n`
(`Curves.traceAddEquiv`). Here `H^2_c(U, μ_n)` is `CompactSupport.H j (mu U n) 2`, the
cohomology of `X` with coefficients in the extension by zero `j_! μ_{n,U}`. The normalization
is that of Aglib's Kummer boundary in `traceAddEquiv`; source-convention comparison is not asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

open Scheme.OverField

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- **The trace `H^2_c(U, μ_n) ≃+ ℤ/n`** of the complement `U` of a finite set of closed points of
the curve, for `n > 0` invertible in `k` (Milne, *Lectures on Étale Cohomology* v2.21,
Prop. 14.5, p. 92): `H^2_c(U, μ_n) ≅ H^2(X, μ_n)` followed by the trace of `X`. -/
def compactSupportTraceAddEquiv (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) : CompactSupport.H.{w} j (mu U n) 2 ≃+ ZMod n :=
  haveI := hX.proper
  (CompactSupport.rootsAddEquiv j n hn hinv D hD hfin hclosed
    (fun x => by
      let := residueAlgebra X.left X.hom x.val
      have : Module.Finite k (X.left.residueField x.val) :=
        residue_finite X.left X.hom ⟨x.val, hclosed x.val x.property⟩
      exact Algebra.IsAlgebraic.isSepClosed (F := k) (E := X.left.residueField x.val))
    2 le_rfl).trans (traceAddEquiv hX n hn hunit hinv)

/-- The compactly supported trace is the trace of the image in `H^2(X, μ_n)`. -/
theorem compactSupportTraceAddEquiv_apply (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) (x : CompactSupport.H.{w} j (mu U n) 2) :
    compactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv x =
      traceAddEquiv hX n hn hunit hinv (CompactSupport.rootsMap j n hn hinv 2 x) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
