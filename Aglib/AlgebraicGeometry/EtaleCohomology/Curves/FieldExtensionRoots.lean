/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FieldExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant.Naturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.DivisibilityReflection

/-! # Original roots pullback for normal proper curves over fields

One base constant-root coordinate and its canonical transport identify the
original roots pullback with the original constant restriction. The existing
proper-curve comparison then supplies all-degree injectivity and, for a
separably closed target, surjectivity. Its standard Ext realization is retained.
The H2 consequence reflects original Picard divisibility. No affine residue
sequence or root-surjectivity of affine units is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k K : Type u) [Field k] [Field K] [IsSepClosed k] [Algebra k K]
  (X : FScheme k) [IsIntegral X.left] [IsProper X.hom]
  (hN : Scheme.NormalStalks X.left) (hdim : topologicalKrullDim X.left = 1)
  (n : ℕ) (hn : 0 < n) (hk : IsUnit (n : Γ(Spec (.of k), ⊤)))

include hN hdim

/-- Original roots cohomology pullback is injective in every degree after
any extension of the separably closed base of a normal integral proper curve. -/
theorem normalProperCurve_fieldExtension_rootsPullback_injective (q : ℕ) :
    Function.Injective (rootsCohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst X.hom (Spec.algebraMap k K)) n hn
        (levelInvertible X.hom n hk) q) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  let f := pullback.fst X.hom (Spec.algebraMap k K)
  let e := constantRootIsoOver k n hn hk X.hom
  let eS := transportConstantRootIso f n hn (levelInvertible X.hom n hk) e
  have hi := normalProperCurve_fieldExtension_constantRestriction_injective
    k K X (ULift.{u} (ZMod n)) hN hdim q
  intro a b hab
  obtain ⟨a', rfl⟩ := (cohomologyMapIso_bijective e q).surjective a
  obtain ⟨b', rfl⟩ := (cohomologyMapIso_bijective e q).surjective b
  apply congrArg (Sheaf.H.map e.hom q)
  apply hi
  apply (cohomologyMapIso_bijective eS q).injective
  exact (transportConstantRootIso_cohomology f n hn
    (levelInvertible X.hom n hk) e q a').trans
      (hab.trans (transportConstantRootIso_cohomology f n hn
        (levelInvertible X.hom n hk) e q b').symm)

/-- With separably closed target, original roots cohomology pullback is
surjective in every degree. The target root coordinate is transported from
the source, not chosen independently. -/
theorem normalProperCurve_fieldExtension_rootsPullback_surjective [IsSepClosed K] (q : ℕ) :
    Function.Surjective (rootsCohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst X.hom (Spec.algebraMap k K)) n hn
        (levelInvertible X.hom n hk) q) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  let f := pullback.fst X.hom (Spec.algebraMap k K)
  let e := constantRootIsoOver k n hn hk X.hom
  let eS := transportConstantRootIso f n hn (levelInvertible X.hom n hk) e
  have hs := (normalProperCurve_fieldExtension_constantRestriction_bijective
    k K X (ULift.{u} (ZMod n)) hN hdim q).surjective
  intro c
  obtain ⟨b, hb⟩ := (cohomologyMapIso_bijective eS q).surjective c
  obtain ⟨a, ha⟩ := hs b
  refine ⟨Sheaf.H.map e.hom q a, ?_⟩
  exact (transportConstantRootIso_cohomology f n hn
    (levelInvertible X.hom n hk) e q a).symm.trans
      ((congrArg (Sheaf.H.map eS.hom q) ha).trans hb)

/-- The original roots pullback is invariant under extension of separably
closed fields, at every positive level invertible in the base field. -/
theorem normalProperCurve_fieldExtension_rootsPullback_bijective [IsSepClosed K] (q : ℕ) :
    Function.Bijective (rootsCohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst X.hom (Spec.algebraMap k K)) n hn
        (levelInvertible X.hom n hk) q) :=
  ⟨normalProperCurve_fieldExtension_rootsPullback_injective k K X hN hdim n hn hk q,
    normalProperCurve_fieldExtension_rootsPullback_surjective k K X hN hdim n hn hk q⟩

include hn hk in
/-- H2 injectivity reflects n-divisibility of original Picard classes of the
proper curve under arbitrary field extension; target separable closure is
not needed for this reflection statement. -/
theorem normalProperCurve_fieldExtension_nsmul_preimage_iff (c : PicardGroup X.left) :
    (∃ b : PicardGroup X.left, n • b = c) ↔
      ∃ b : PicardGroup (pullback X.hom (Spec.algebraMap k K)),
        n • b = pullbackClass (pullback.fst X.hom (Spec.algebraMap k K)) c :=
  Picard.nsmul_preimage_iff_of_rootsH2_injective
    (pullback.fst X.hom (Spec.algebraMap k K)) n hn (levelInvertible X.hom n hk)
    (normalProperCurve_fieldExtension_rootsPullback_injective k K X hN hdim n hn hk 2) c

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
