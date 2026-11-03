/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.Complement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteConstantAnnihilator
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Standard

/-! # Ordinary higher finite-constant cohomology on an open curve

The imported geometric root-coefficient vanishing is transported through one
native constant-root coordinate. The existing annihilator-bounded cyclic
reduction and positive acyclicity of the algebraically closed field supply
arbitrary finite constants, without a second direct-sum implementation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w

attribute [local instance] hasSheafifyLarge HasExt.standard

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : FScheme k} (hX : Curve.Properties X)
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} U)]

include hX

/-- Original cyclic-constant cohomology vanishes in every degree at least two
on the specified noncomplete open of the original algebraically closed curve. -/
theorem cyclicConstant_subsingleton_H_of_isOpenImmersion
    (hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) q) := by
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  have hk : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  let e := Kummer.HenselianConstant.constantRootIsoOver k n hn hk (j ≫ X.hom)
  have h := roots_subsingleton_H_of_isOpenImmersion hX j hx n hunit q hq
  refine ⟨fun a b => ?_⟩
  apply (cohomologyMapIso_bijective e q).injective
  exact h.elim _ _

/-- All ordinary finite constant coefficients with a positive invertible
annihilator have zero higher cohomology on the specified original open curve.
The original target Ext universe is arbitrary. -/
theorem finiteConstant_subsingleton_H_of_isOpenImmersion
    (hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (_hn : 0 < n) (hkill : ∀ a : A, n • a = 0)
    (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient A U) q) := by
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  have hsurj : Function.Surjective
      (constantRestriction.{u, u + 2, w} A (j ≫ X.hom) q) := by
    apply constantRestriction_surjective_of_cyclic_divisors (j ≫ X.hom) q n _ A hkill
    intro m hm hmn
    have hmUnit : IsUnit (m : k) := by
      apply isUnit_of_dvd_unit _ hunit
      obtain ⟨d, hd⟩ := hmn
      exact ⟨(d : k), by rw [hd, Nat.cast_mul]⟩
    have hz := cyclicConstant_subsingleton_H_of_isOpenImmersion hX j hx m hm hmUnit q hq
    intro a
    exact ⟨0, hz.elim _ _⟩
  have hz := StrictlyLocal.subsingleton_H_standard.{u, u + 2} k
    (ConstantFinite.coefficient A (Spec (.of k))) q (by omega)
  refine ⟨fun a b => ?_⟩
  obtain ⟨a₀, rfl⟩ := hsurj a
  obtain ⟨b₀, rfl⟩ := hsurj b
  exact congrArg (constantRestriction.{u, u + 2, w} A (j ≫ X.hom) q) (hz.elim a₀ b₀)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
