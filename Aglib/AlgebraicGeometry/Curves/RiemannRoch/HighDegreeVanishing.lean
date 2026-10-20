/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.NegativeDegree
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Invertible
public import Aglib.AlgebraicGeometry.Curves.RiemannHurwitz.CanonicalDegree
public import Aglib.AlgebraicGeometry.Curves.Regular
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# High-degree vanishing on the original proper regular field curve

This constructs the unchanged `LineBundleHighDegreeVanishing` family from
`R5Lab/Aglib/AlgebraicGeometry/Curves/RiemannRoch.lean:92–99` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, now owned by the native curve namespace.
The original degree, canonical bundle, structural map and cohomology are retained.

The original integral Noetherian dimension-one scheme with closed DVR stalks
has regular stalks everywhere. Over the original algebraically closed field
it is smooth, and an actual closed DVR point in every standard-smooth chart
forces relative dimension one. Properness supplies the original constants
bijection and the proved projective embedding.

Actual Serre duality and the structural-linear degree-zero Ext comparison
identify the dual of the original H¹ with H⁰ of the canonical line bundle
tensored with the original dual line bundle. Its original degree is negative
when `deg L ≥ 2g−1`, so the actual negative-degree theorem kills it.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.OverField.Curve

universe u

open Divisors

/-- The literal original all-genus high-degree vanishing family. -/
theorem lineBundleHighDegreeVanishing : LineBundleHighDegreeVanishing.{u} := by
  intro K hK hclosed X hInt hNoeth hDVR hdim hprod L hp hL
  let := hp
  obtain ⟨hsmooth, hc⟩ := regularCurve_smoothAndConstants K X hdim hp
  let N := tensorLineBundle X.left (canonicalLineBundle X hsmooth) (dualLineBundle X.left L)
  have hN : Picard.Degree.lineBundleDegree X.left X.hom hdim.le hprod N < 0 := by
    dsimp only [N]
    rw [Picard.Degree.lineBundleDegree_tensor, Picard.Degree.lineBundleDegree_dual,
      smoothCanonicalDegree K X hdim.le hprod hsmooth hp hc]
    omega
  have := lineBundleH0_subsingleton_of_neg_degree X hdim.le hprod N hN
  let := moduleCategoryLinearOfHom X.left (Scheme.constants X)
  let E : Ext.{u + 1} (C := X.left.Modules) L.val (differentialSheaf X) 0 ≃ₗ[K]
      moduleCohomology K X N.val 0 :=
    lineBundleExtZeroEquivH0 X L (differentialSheaf X)
  have : Subsingleton (Ext.{u + 1} (C := X.left.Modules) L.val (differentialSheaf X) 0) :=
    E.injective.subsingleton
  obtain ⟨n, i, hi, hbase⟩ := Projectivity.exists_projectiveEmbedding X hdim
  let := hi
  have hM : affineLocallyFiniteType X.left L.val :=
    (affineLocallyFiniteType_iff_finitePresentation L.val).mpr
      (lineBundle_isFinitePresentation X.left L)
  let D := Duality.actualCanonicalExtDuality _ n Equiv.ulift X i hbase hsmooth
    L.val hM (genericPoint X.left) 0 1 (by omega)
  have : Subsingleton (Module.Dual K (moduleCohomology K X L.val 1)) :=
    D.symm.injective.subsingleton
  let : Module.Projective K (moduleCohomology K X L.val 1) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace K (moduleCohomology K X L.val 1))
  exact (Module.subsingleton_dual_iff K).mp inferInstance

/-- A direct consumer on the original line bundle, with exactly the original
geometric, degree and cohomology objects. -/
theorem lineBundleH1_subsingleton_of_high_degree
    (K : Type u) [Field K] [IsAlgClosed K] (X : FScheme K)
    [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left = 1)
    (hprod : Picard.Degree.PrincipalProductFormula X.left X.hom)
    (L : LineBundle X.left) (hp : IsProper X.hom)
    (hL : 2 * (coherentGenus K X : ℤ) - 1 ≤
      Picard.Degree.lineBundleDegree X.left X.hom hdim.le hprod L) :
    Subsingleton (moduleCohomology K X L.val 1) :=
  lineBundleHighDegreeVanishing K X hdim hprod L hp hL

end AlgebraicGeometry.Scheme.OverField.Curve
