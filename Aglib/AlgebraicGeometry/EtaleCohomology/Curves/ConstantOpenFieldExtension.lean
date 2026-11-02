/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.KummerOpenFieldExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteConstantAnnihilator
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant.Naturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Mathlib.Algebra.Divisibility.Units

/-! # Original finite constant H1 comparison on open curves

One actual base constant-root coordinate and its transported target identify
cyclic constant comparison with the original roots comparison. The native
finite split-family construction then handles finite constant coefficients
annihilated by an invertible positive integer, using only its cyclic divisors.
No characteristic-primary or arbitrary finite-locally-constant comparison is
asserted.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.ConstantOpenFieldExtension

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
  (X : FScheme k) (hX : Curve.Properties X)
  {U : Scheme.{u}} [Nonempty U] (j : U ⟶ X.left) [IsOpenImmersion j]

include hX in
/-- Original cyclic constant H1 restriction is surjective, using only one
source root coordinate and its canonical target transport. -/
theorem cyclic_constantRestriction_surjective (n : ℕ) (hn : 0 < n)
    (hk : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    Function.Surjective (constantRestriction.{u, u + 2, u + 2} (ULift.{u} (ZMod n))
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) 1) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  let f := pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)
  let hi := levelInvertible j n (levelInvertible X.hom n hk)
  let e := constantRootIsoOver k n hn hk (j ≫ X.hom)
  let eS := transportConstantRootIso f n hn hi e
  have hs := KummerOpenFieldExtension.h1Map_surjective k K X hX j n hn hk
  intro c
  obtain ⟨b, hb⟩ := hs (Sheaf.H.map eS.hom 1 c)
  obtain ⟨a, ha⟩ := (cohomologyMapIso_bijective e 1).surjective b
  refine ⟨a, (cohomologyMapIso_bijective eS 1).injective ?_⟩
  exact (transportConstantRootIso_cohomology f n hn hi e 1 a).trans
    ((congrArg (h1Map f n hn hi) ha).trans hb)

omit [Nonempty U] [IsOpenImmersion j] [IsAlgClosed K] in
/-- Original constant H1 restriction is injective for every finite coefficient,
using the native finite-constant trivialization and actual geometric descent. -/
theorem constantRestriction_injective (A : Type u) [AddCommGroup A] [Finite A] :
    Function.Injective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) 1) := by
  let f := pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)
  have hF : IsFiniteLocallyConstant (ConstantFinite.coefficient A U) :=
    ⟨Constructible.finiteConstantTrivialization U (ConstantFinite.value A)⟩
  exact (coefficientIso ((inverseImageConstantIso f).app (ConstantFinite.value A))).injective.comp
    (h1Pullback_injective_fieldExtension k K (j ≫ X.hom)
      (ConstantFinite.coefficient A U) hF)

include hX in
/-- Finite constant H1 is invariant on a nonempty open of the original smooth
proper curve when an actual positive annihilator is invertible on the base. -/
theorem constantRestriction_bijective (A : Type u) [AddCommGroup A] [Finite A]
    (N : ℕ) (hpos : 0 < N) (hN : ∀ a : A, N • a = 0)
    (hk : IsUnit (N : Γ(Spec (.of k), ⊤))) :
    Function.Bijective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) 1) := by
  refine ⟨constantRestriction_injective k K X j A, ?_⟩
  apply constantRestriction_surjective_of_cyclic_divisors
    (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K)) 1 N _ A hN
  intro m _hm hmN
  have hm : 0 < m := Nat.pos_of_dvd_of_pos hmN hpos
  have hmk : IsUnit (m : Γ(Spec (.of k), ⊤)) := by
    apply isUnit_of_dvd_unit _ hk
    obtain ⟨d, hd⟩ := hmN
    exact ⟨(d : Γ(Spec (.of k), ⊤)), by rw [hd, Nat.cast_mul]⟩
  exact cyclic_constantRestriction_surjective k K X hX j m hm hmk

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.ConstantOpenFieldExtension
