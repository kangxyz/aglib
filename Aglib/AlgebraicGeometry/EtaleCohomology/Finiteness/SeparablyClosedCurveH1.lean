/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PurelyInseparable.ProjectionH1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.PrimeToCharacteristicCurveH1
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Finite original H1 over separably closed constants

A separably closed field need not be perfect. Its algebraic closure is purely
inseparable, so original constant H1 injects into the finite algebraically
closed value. The constant/root coefficient isomorphism gives roots H1 over
the original field, without replacing smoothness by regularity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness

universe u w

attribute [local instance] hasSheafifyLarge

/-- Positive invertible cyclic original H1 is finite on a smooth proper
geometrically connected curve over a separably closed, possibly imperfect field.
The original source Ext universe is arbitrary. -/
theorem finite_cyclic_h1_of_separably_closed_smooth_proper_curve
    {k : Type u} [Field k] [IsSepClosed k]
    (X : FScheme k) (hX : Properties X) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] :
    Finite (H1Etale.{u, u + 1, w} X.left
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left)) := by
  let : NeZero n := ⟨hn.ne'⟩
  let : IsProper X.hom := hX.proper
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let Ω := AlgebraicClosure k
  let a := Spec.algebraMap k Ω
  let XΩ : FScheme Ω := Over.mk (pullback.snd X.hom a)
  let f : XΩ.left ⟶ X.left := pullback.fst X.hom a
  let targetExt : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} XΩ.left) :=
    hasExtStandard.{u, u + 1} XΩ.left
  have hΩ : Properties XΩ := curveProperties_baseChange hX Ω a
  have hunitΩ : IsUnit (n : Ω) := by
    simpa only [map_natCast] using hunit.map (algebraMap k Ω)
  let : Finite (H1Etale.{u, u + 1, u + 2} XΩ.left
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) XΩ.left)) :=
    finite_cyclic_h1_of_smooth_proper_curve XΩ hΩ n hn hunitΩ
  exact Finite.of_injective (ConstantFinite.pullbackH1 (ULift.{u} (ZMod n)) f)
    (@Fields.PurelyInseparable.constantH1Pullback_injective.{u, w, u + 2}
      k Ω inferInstance inferInstance inferInstance inferInstance X.left
      inferInstance inferInstance X.hom inferInstance targetExt
      (ULift.{u} (ZMod n)) inferInstance inferInstance)

/-- Positive invertible roots of unity have finite original H1 on a smooth
proper geometrically connected curve over any separably closed field. -/
theorem finite_roots_h1_of_separably_closed_smooth_proper_curve
    {k : Type u} [Field k] [IsSepClosed k]
    (X : FScheme k) (hX : Properties X) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)] :
    Finite (H1Etale.{u, u + 1, w} X.left (mu X.left n)) := by
  let : Finite (H1Etale.{u, u + 1, w} X.left
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X.left)) :=
    finite_cyclic_h1_of_separably_closed_smooth_proper_curve X hX n hn hunit
  have hinv : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  let e := coefficientIso
    (Kummer.HenselianConstant.constantRootIsoOver k n hn hinv X.hom).symm
  exact Finite.of_injective e e.injective

end AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness
