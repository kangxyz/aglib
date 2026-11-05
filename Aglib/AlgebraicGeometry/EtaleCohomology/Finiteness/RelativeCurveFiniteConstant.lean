/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.MixedCharacteristicCurveHigher
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.RelativeCurveFiniteConstantR2
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.RelativeCurveFiniteConstantR1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperConstantDegreeZero

/-! # All finite-constant images of proper relative curves

The fixed degrees zero, one, and two use their original complete endpoints.
Higher degrees use the actual prime-power theorem and the same finite-product
coefficient property. No all-degree extension-closure premise is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Every finite abelian constant has constructible higher images in every degree. -/
theorem finiteConstantHigherDirectImage_isConstructible_of_relativeCurve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (q : ℕ) (A : Type u) [AddCommGroup A] [Finite A] :
    Constructible.IsConstructible ((higherDirectImage f q).obj
      (ConstantFinite.coefficient A X)) := by
  classical
  by_cases h0 : q = 0
  · subst q
    exact (Constructible.isConstructible_iff_of_iso
      ((directImage f).rightDerivedZeroIsoSelf.app _)).mpr
      (isConstructible_properDirectImage f
        (Constructible.isConstructible_constant X (ConstantFinite.value A)))
  by_cases h1 : q = 1
  · subst q
    exact finiteConstantHigherDirectImage_R1_isConstructible_of_relativeCurve_unrestricted
      f hdim A
  by_cases h2 : q = 2
  · subst q
    exact finiteConstantHigherDirectImage_R2_isConstructible_of_relativeCurve_unrestricted
      f hdim A
  have hq : 2 < q := by omega
  obtain ⟨I, hI, p, hp, r, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let := hI
  apply AddCommGrpCat.prop_of_zmod_directSum_equiv_of_finiteProducts
    (FiniteConstantImage.property f q) (fun i => p i ^ r i) e
  intro i
  exact cyclicPrimePowerHigherDirectImage_isConstructible_of_relativeCurve_above_two
    f hdim (p i) (hp i) (r i) q hq

end AlgebraicGeometry.Scheme.EtaleCohomology
