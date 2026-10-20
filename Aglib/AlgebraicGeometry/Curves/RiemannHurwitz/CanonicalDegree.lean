/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Duality
public import Aglib.AlgebraicGeometry.Curves.RiemannHurwitz
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.LineBundle
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Integral
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Canonical degree from actual curve duality

The original integral proper curve admits a proved projective embedding over its
original field. Actual canonical duality identifies `H⁰(Ω)` with the dual of
`H¹(O)` and `H¹(Ω)` with the dual of `H⁰(O)`. The supplied constants bijection
makes the latter dimension one. The proved Riemann–Roch formula then gives
canonical degree `2g - 2` for the existing residue-weighted divisor/Picard degree.

The final factory realizes the unchanged all-field `SmoothCanonicalDegree`
interface from `Curves/RiemannHurwitz.lean:144`. It retains its actual canonical
line bundle, smoothness, properness, closed DVR stalks, dimension bound, principal
product formula and constants hypotheses. Its native duality source basis is
Aglib `64374534558c80c2fec996ee06bf7727b6c7f3e4`; the actual degree and genus
construction and the proved projectivity and Riemann–Roch theorems are R5Lab's
existing curve objects.
-/




@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u

/-- Numerical canonical degree on the original curve through a proved actual embedding. -/
theorem smoothCanonicalDegree_of_projectiveEmbedding
    (F : Type u) [Field F] (X : FScheme F) [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : Scheme.ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X.left X.hom)
    (hsmooth : SmoothOfRelativeDimension 1 X.hom)
    (hproper : IsProper X.hom) (hc : Function.Bijective (AlgebraicGeometry.Scheme.constants X))
    (n : ℕ) (i : X.left ⟶ ProjectiveSpace F (ULift.{u} (Fin (n + 1))))
    [IsClosedImmersion i]
    (hbase : i ≫ ProjectiveSpace.toSpec F (ULift.{u} (Fin (n + 1))) = X.hom) :
    Picard.Degree.lineBundleDegree X.left X.hom hdim hprod (canonicalLineBundle X hsmooth) =
      2 * (coherentGenus F X : ℤ) - 2 := by
  let e : ULift.{u} (Fin (n + 1)) ≃ Fin (n + 1) := Equiv.ulift
  let e0 := Duality.actualCanonicalCohomologyDuality _ n e X i hbase hsmooth
    (genericPoint X.left) 0 1 (by omega)
  let e1 := Duality.actualCanonicalCohomologyDuality _ n e X i hbase hsmooth
    (genericPoint X.left) 1 0 (by omega)
  have h0 : Module.finrank F (moduleCohomology F X (differentialSheaf X) 0) =
      coherentGenus F X := by
    have h := e0.finrank_eq
    rw [Subspace.dual_finrank_eq] at h
    exact h
  let ec := (structureModuleCohomologyEquiv X 0).symm.trans
    (Picard.DivisorClass.structureModuleH0ConstantsEquiv X hc)
  have hc0 : Module.finrank F (AlgebraicGeometry.Scheme.structureCohomology F X 0) = 1 := by
    rw [ec.finrank_eq, Module.finrank_self]
  have h1 : Module.finrank F (moduleCohomology F X (differentialSheaf X) 1) = 1 := by
    have h := e1.finrank_eq
    rw [Subspace.dual_finrank_eq, hc0] at h
    exact h
  have hrr := lineBundleRiemannRoch F X hdim hprod (canonicalLineBundle X hsmooth) hproper hc
  change (Module.finrank F (moduleCohomology F X (differentialSheaf X) 0) : ℤ) -
      (Module.finrank F (moduleCohomology F X (differentialSheaf X) 1) : ℤ) =
    Picard.Degree.lineBundleDegree X.left X.hom hdim hprod (canonicalLineBundle X hsmooth) +
      1 - (coherentGenus F X : ℤ) at hrr
  rw [h0, h1] at hrr
  omega

/-- The unchanged all-field original SmoothCanonicalDegree interface. -/
theorem smoothCanonicalDegree : SmoothCanonicalDegree.{u} := by
  intro F hF X hInt hNoeth hDVR hdim hprod hsmooth hproper hc
  let := hproper
  have hdimeq := dimension_eq_one_of_closedDVR X hdim
  obtain ⟨n, i, hi, hbase⟩ := Projectivity.exists_projectiveEmbedding X hdimeq
  let := hi
  exact smoothCanonicalDegree_of_projectiveEmbedding F X hdim hprod hsmooth hproper hc n i hbase

end AlgebraicGeometry.Scheme.OverField.Curve
