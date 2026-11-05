/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.MixedCharacteristicCurveR1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.FiniteConstantImageProperty
public import Aglib.Algebra.Category.Grp.FiniteProperty

/-! # Fixed-degree finite-constant R1 for proper relative curves

The original finite abelian coefficient is decomposed by the native finite
cyclic decomposition. Only finite-product preservation in this one degree is
used, not an all-degree extension or Serre hypothesis. The original positive
invertible-annihilator API is retained. The unrestricted endpoint consumes the
actual mixed-characteristic prime-power producer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Finite constants with a positive invertible annihilator have constructible
original first higher image under a proper relative curve. -/
theorem finiteConstantHigherDirectImage_R1_isConstructible_of_relativeCurve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (A : Type u) [AddCommGroup A] [Finite A]
    (N : ℕ) (_hNpos : 0 < N) (hNunit : IsUnit (N : Γ(S, ⊤)))
    (hN : ∀ a : A, N • a = 0) :
    Constructible.IsConstructible ((higherDirectImage f 1).obj
      (ConstantFinite.coefficient A X)) := by
  classical
  let P := FiniteConstantImage.property f 1
  apply AddCommGrpCat.prop_of_finite_of_cyclic_divisors_of_finiteProducts P N ?_ A hN
  intro m hm hmN
  have hunit : IsUnit (m : Γ(S, ⊤)) :=
    isUnit_of_dvd_unit (by
      obtain ⟨a, ha⟩ := hmN
      refine ⟨(a : Γ(S, ⊤)), ?_⟩
      simpa only [Nat.cast_mul] using congrArg (fun k : ℕ => (k : Γ(S, ⊤))) ha) hNunit
  exact cyclicHigherDirectImage_R1_isConstructible_of_relativeCurve f hdim m hm hunit

/-- Every actual finite abelian constant has constructible original R1 for a
proper relative curve on a Noetherian base, without an invertibility or
characteristic hypothesis. This remains a fixed-degree theorem. -/
theorem finiteConstantHigherDirectImage_R1_isConstructible_of_relativeCurve_unrestricted
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (A : Type u) [AddCommGroup A] [Finite A] :
    Constructible.IsConstructible ((higherDirectImage f 1).obj
      (ConstantFinite.coefficient A X)) := by
  classical
  obtain ⟨I, hI, p, hp, r, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let := hI
  apply AddCommGrpCat.prop_of_zmod_directSum_equiv_of_finiteProducts
    (FiniteConstantImage.property f 1) (fun i => p i ^ r i) e
  intro i
  exact cyclicPrimePowerHigherDirectImage_R1_isConstructible_of_relativeCurve f hdim
    (p i) (hp i) (r i)

end AlgebraicGeometry.Scheme.EtaleCohomology
