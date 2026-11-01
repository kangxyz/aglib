/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.FiniteProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.HigherImageConstructibleExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CyclicCoefficientSequence

/-! # Original constant-coefficient constructibility reductions

Genuine cyclic extensions and the native finite abelian decomposition propagate
all-degree constructibility of original higher images. These reductions impose
no geometric hypotheses and do not import a proper-base-change producer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- All-degree constructibility for the original cyclic prime coefficient
propagates through the actual cyclic extensions. The exponent-zero coefficient
is the actual zero object. No geometric hypotheses are needed for this step. -/
theorem cyclicPrimePowerHigherDirectImage_isConstructible_of_prime
    {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ) (hp : 0 < p)
    (hprime : ∀ q : ℕ, Constructible.IsConstructible
      ((higherDirectImage f q).obj (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X)))
    (r q : ℕ) : Constructible.IsConstructible
      ((higherDirectImage f q).obj
        (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r))) X)) := by
  induction r generalizing q with
  | zero =>
      change Constructible.IsConstructible
        ((higherDirectImage f q).obj
          ((Curves.cyclicCoefficientFunctor X).obj (AddCommGrpCat.of (ZMod 1))))
      exact ObjectProperty.prop_of_isZero (Constructible.IsConstructible (X := S))
        ((higherDirectImage f q).map_isZero
          ((Curves.cyclicCoefficientFunctor X).map_isZero
            (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (ZMod 1)))))
  | succ r ih =>
      have h := higherDirectImage_isConstructible_of_shortExact f
        ((ZMod.mulSequence (p ^ r) p).map (Curves.cyclicCoefficientFunctor X))
        (Curves.cyclicCoefficient_shortExact X (p ^ r) p hp) ih hprime q
      change Constructible.IsConstructible
        ((higherDirectImage f q).obj
          (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ r * p))) X)) at h
      exact Eq.mpr (congrArg (fun n : ℕ => Constructible.IsConstructible
        ((higherDirectImage f q).obj
          (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X))) (pow_succ p r)) h

/-- Original all-degree constant-coefficient constructibility reduces to the
positive cyclic divisors of the actual annihilator. No geometric hypotheses
are needed for this finite-abelian reduction. -/
theorem constantHigherDirectImage_isConstructible_of_cyclic_divisors
    {X S : Scheme.{u}} (f : X ⟶ S) (N : ℕ)
    (hcyclic : ∀ m : ℕ, 0 < m → m ∣ N → ∀ q : ℕ,
      Constructible.IsConstructible ((higherDirectImage f q).obj
        (ConstantFinite.coefficient (ULift.{u} (ZMod m)) X)))
    (A : Type u) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0)
    (q : ℕ) : Constructible.IsConstructible
      ((higherDirectImage f q).obj (ConstantFinite.coefficient A X)) := by
  let C : AddCommGrpCat.{u} ⥤ AbelianSheaf.{u, u + 1} X :=
    AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
      constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : C.Additive := by dsimp [C, constantSheaf]; infer_instance
  let : PreservesFiniteLimits C := by dsimp [C, constantSheaf]; infer_instance
  let : PreservesFiniteColimits C := by dsimp [C, constantSheaf]; infer_instance
  let P : ObjectProperty AddCommGrpCat.{u} := fun B =>
    ∀ n : ℕ, Constructible.IsConstructible ((higherDirectImage f n).obj (C.obj B))
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h n =>
    (Constructible.isConstructible_iff_of_iso
      ((higherDirectImage f n).mapIso (C.mapIso e))).mp (h n)⟩
  let : P.ContainsZero := { exists_zero := ⟨0, isZero_zero _, fun n =>
    ObjectProperty.prop_of_isZero (Constructible.IsConstructible (X := S))
      ((higherDirectImage f n).map_isZero (C.map_isZero (isZero_zero _)))⟩ }
  let : P.IsClosedUnderExtensions := ⟨fun hT h₁ h₃ n =>
    higherDirectImage_isConstructible_of_shortExact f _ (hT.map_of_exact C) h₁ h₃ n⟩
  exact AddCommGrpCat.prop_of_finite_of_cyclic_divisors P N hcyclic A hN q

end AlgebraicGeometry.Scheme.EtaleCohomology
