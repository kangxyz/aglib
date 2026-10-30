/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CurveCohomology.Trace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.UnitsQuotient
public import Aglib.AlgebraicGeometry.Picard.KummerH1
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The cohomology of `μ_n` and `ℤ/n` on a smooth proper curve

Let `k` be an algebraically closed field, `X` a smooth proper geometrically connected curve over
`k` (`Curve.Properties X`) and `n` a positive integer invertible in `k`. Then
(Stacks, Étale Cohomology, Lemma 69.1, Tag 03RQ; Milne, *Lectures on Étale Cohomology* v2.21,
Prop. 14.2, p. 90):

* `rootsZeroAddEquiv`: `H^0(X, μ_n) ≃+ μ_n(k)`, through the global sections of `μ_n` and the
  constants `k ≃ Γ(X, 𝒪_X)` of the proper geometrically integral `X` (for every `n`);
* `rootsOneAddEquiv`: `H^1(X, μ_n) ≃+ Pic(X)[n]`, the Kummer classification
  `KummerH1.h1PicardTorsionEquiv`, whose global-root hypothesis holds because the global units
  are `k^×`. `rootsOneAddEquiv_subtype` identifies its whole underlying Picard map with the
  original Kummer inclusion followed by the Picard comparison;
* `traceAddEquiv` (in `CurveCohomology.Trace`): `H^2(X, μ_n) ≃+ ℤ/n`;
* `roots_subsingleton_H_of_curve` (in `Curves.PrimeToCharacteristicVanishing`):
  `H^q(X, μ_n) = 0` for `q ≥ 3`.

With constant coefficients `ℤ/n` (the finite constant sheaf `ConstantFinite.coefficient` of
`ULift (ZMod n)`), `constantRootsAddEquiv` transports every degree through the isomorphism
`ℤ/n ≅ μ_n` over the algebraically closed `k` (`HenselianConstant.constantRootIsoOver`, a choice
of primitive root of unity), giving `constantZeroAddEquiv`, `constantOneAddEquiv`,
`constantTwoAddEquiv` and `constant_subsingleton_H_of_curve`. The ranks of `Pic(X)[n]` are not
treated here.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

open Scheme.OverField

variable {k : Type u} [Field k] {X : FScheme k} (hX : Curve.Properties X)

/-- The constants `k ≃+* Γ(X, 𝒪_X)` of a smooth proper geometrically connected curve. -/
def constantsRingEquiv : k ≃+* Γ(X.left, ⊤) :=
  haveI := hX.proper
  haveI := hX.isGeometricallyIntegral
  RingEquiv.ofBijective (Scheme.constants X) (constants_bijective_of_proper_geometricallyIntegral X)

@[simp] theorem constantsRingEquiv_apply (a : k) :
    constantsRingEquiv hX a = Scheme.constants X a := rfl

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

/-- **`H^0(X, μ_n) ≃+ μ_n(k)`** (Stacks, Étale Cohomology, Lemma 69.1, Tag 03RQ, `q = 0`):
degree-zero cohomology is the group of global sections, the global roots of unity of
`Γ(X, 𝒪_X)`, which are those of `k` through the constants. -/
def rootsZeroAddEquiv (n : ℕ) : Sheaf.H.{w} (mu X.left n) 0 ≃+ Additive (rootsOfUnity n k) :=
  (Sheaf.H.equiv₀ (mu X.left n) (etaleTerminalIsTerminal X.left)).trans
    ((rootsSections X.left n (op (etaleTerminal X.left))).trans
      (MulEquiv.restrictRootsOfUnity (constantsRingEquiv hX).symm.toMulEquiv n).toAdditive)

variable [IsAlgClosed k]

/-- **`H^1(X, μ_n) ≃+ Pic(X)[n]`** (Stacks, Étale Cohomology, Lemma 69.1, Tag 03RQ, `q = 1`), for
`n > 0` invertible on `X`: the Kummer classification `KummerH1.h1PicardTorsionEquiv`, whose
hypothesis that every global unit is an `n`-th power holds because the global units are `k^×`. -/
def rootsOneAddEquiv (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    Sheaf.H.{w} (mu X.left n) 1 ≃+ Torsion.picardTorsion X.left n :=
  haveI := hX.proper
  haveI := hX.isIntegral
  haveI := hX.isGeometricallyIntegral
  haveI := Curve.curveProperties_isNoetherian hX
  haveI (x : Scheme.ClosedPoint X.left) := Curve.PointDivisor.isDiscreteValuationRing_stalk X hX x
  KummerH1.h1PicardTorsionEquiv X.left EtaleDescent.etaleLineBundleDescent (stacks03AJ X.left) n
    hn hinv (TrivializedPower.globalUnits_pow_surjective X.left X.hom
      (constants_bijective_of_proper_geometricallyIntegral X).2 n hn)

/-- The whole proper H1 equivalence retains the original roots-to-Picard map. -/
theorem rootsOneAddEquiv_subtype (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    (Torsion.picardTorsion X.left n).subtype.comp
        (rootsOneAddEquiv hX n hn hinv).toAddMonoidHom = Kummer.rootsPicardMap X.left n := by
  have := hX.proper
  have := hX.isIntegral
  have := hX.isGeometricallyIntegral
  have := Curve.curveProperties_isNoetherian hX
  have (x : Scheme.ClosedPoint X.left) := Curve.PointDivisor.isDiscreteValuationRing_stalk X hX x
  let hroot := TrivializedPower.globalUnits_pow_surjective X.left X.hom
    (constants_bijective_of_proper_geometricallyIntegral X).2 n hn
  apply AddMonoidHom.ext
  intro x
  obtain ⟨P, rfl⟩ := KummerH1.pairClassToH1_surjective X.left
    EtaleDescent.etaleLineBundleDescent (stacks03AJ X.left) n hn hinv x
  induction P using Quotient.inductionOn with
  | h P =>
    change (KummerH1.h1PicardTorsionEquiv X.left EtaleDescent.etaleLineBundleDescent
      (stacks03AJ X.left) n hn hinv hroot
      (torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
        X.left n hn hinv P))).val = _
    rw [KummerH1.h1PicardTorsionEquiv_torsor]
    apply (Picard.picardCohomologyEquiv X.left).injective
    change Picard.picardCohomologyEquiv X.left (classOf X.left P.lineBundle) =
      Picard.picardCohomologyEquiv X.left ((Picard.picardCohomologyEquiv X.left).symm
        (Sheaf.H.map (inclusion X.left n) 1
          (torsorExtClass (TrivializedPowerTorsor.torsor EtaleDescent.etaleLineBundleDescent
            X.left n hn hinv P))))
    rw [AddEquiv.apply_symm_apply]
    exact (KummerH1.pairClassToH1_forget X.left EtaleDescent.etaleLineBundleDescent
      n hn hinv (Quotient.mk _ P)).symm

/-- The isomorphism `ℤ/n ≅ μ_n` of étale sheaves on `X` over the algebraically closed `k`
(`HenselianConstant.constantRootIsoOver`), for `n > 0` invertible in `k`. -/
def constantRootIso (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left ≅ mu X.left n :=
  haveI : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  Kummer.HenselianConstant.constantRootIsoOver k n hn
    (by simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom) X.hom

/-- **`H^q(X, ℤ/n) ≃+ H^q(X, μ_n)`** in every degree, through `constantRootIso`. -/
def constantRootsAddEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) :
    Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) q ≃+
      Sheaf.H.{w} (mu X.left n) q :=
  ((Sheaf.functorH (Scheme.smallEtaleTopology X.left) q).mapIso
    (constantRootIso (X := X) n hn hunit)).addCommGroupIsoToAddEquiv

theorem constantRootsAddEquiv_apply (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ)
    (a : Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) q) :
    constantRootsAddEquiv (X := X) n hn hunit q a =
      Sheaf.H.map (constantRootIso (X := X) n hn hunit).hom q a := rfl

/-- `H^0(X, ℤ/n) ≃+ μ_n(k)`, through `ℤ/n ≅ μ_n`. -/
def constantZeroAddEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 0 ≃+
      Additive (rootsOfUnity n k) :=
  (constantRootsAddEquiv n hn hunit 0).trans (rootsZeroAddEquiv hX n)

/-- `H^1(X, ℤ/n) ≃+ Pic(X)[n]`, through `ℤ/n ≅ μ_n`. -/
def constantOneAddEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 1 ≃+
      Torsion.picardTorsion X.left n :=
  (constantRootsAddEquiv n hn hunit 1).trans (rootsOneAddEquiv hX n hn hinv)

/-- `H^2(X, ℤ/n) ≃+ ℤ/n`, the trace through `ℤ/n ≅ μ_n`. -/
def constantTwoAddEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) 2 ≃+ ZMod n :=
  (constantRootsAddEquiv n hn hunit 2).trans (traceAddEquiv hX n hn hunit hinv)

include hX in
/-- **`H^q(X, ℤ/n) = 0` for `q ≥ 3`**, from `roots_subsingleton_H_of_curve` through
`ℤ/n ≅ μ_n`. -/
theorem constant_subsingleton_H_of_curve (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left) q) := by
  have := Curve.curveProperties_locallyOfFiniteType hX
  have := hX.proper
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have := roots_subsingleton_H_of_curve k X.left X.hom hX.topologicalKrullDim_eq_one.le n hn hunit
    hinv q hq
  exact (constantRootsAddEquiv n hn hunit q).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
