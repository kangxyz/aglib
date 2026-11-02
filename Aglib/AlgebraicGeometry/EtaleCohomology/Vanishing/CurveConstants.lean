/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CharacteristicPrimaryGeometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CyclicVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # All positive cyclic coefficients on arbitrary proper curves

The geometric cases already exist separately: Kummer roots above degree two,
and characteristic-primary constants above degree one. Here they are joined
using the original cyclic short exact sequences. Neither smoothness nor
reducedness nor perfectness nor invertibility of the modulus is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge

/-- Every positive original cyclic constant coefficient has zero cohomology
above degree two on a proper dimension-at-most-one scheme over a separably
closed field, with the original Ext universe arbitrary. -/
theorem constantCyclic_subsingleton_H_of_proper_dimension_le_one
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (n : ℕ) (hn : 0 < n) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{e}
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X) q) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  apply Curves.cyclic_vanishing_of_prime_divisors X q n hn
  intro p hp _
  let : Fact p.Prime := ⟨hp⟩
  by_cases hz : (p : k) = 0
  · let : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hz
    let Y : Scheme.OverField.FScheme k := CategoryTheory.Over.mk f
    let : IsProper Y.hom := inferInstanceAs (IsProper f)
    let : HasExt.{e} (AbelianSheaf.{u, u + 1} Y.left) :=
      inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} X))
    have h := Curves.characteristicPrimary_vanishing.{u, e} Y hdim p (q - 2) 1
    change Subsingleton (Sheaf.H.{e}
      (ConstantFinite.coefficient (ULift.{u} (ZMod (p ^ 1))) X) (q - 2 + 2)) at h
    have hq' : q - 2 + 2 = q := by omega
    rw [hq'] at h
    exact Eq.mp (congrArg (fun n : ℕ => Subsingleton (Sheaf.H.{e}
      (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X) q)) (pow_one p)) h
  · have hu : IsUnit (p : k) := isUnit_iff_ne_zero.mpr hz
    have hbase : IsUnit (p : Γ(Spec (.of k), ⊤)) := by
      simpa using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom
    have htarget : IsUnit (p : Γ(X, ⊤)) := levelInvertible f p hbase
    let : HenselianLocalRing k := Field.henselian _
    let : IsSepClosed (IsLocalRing.ResidueField k) :=
      Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
    let rootIso := Kummer.HenselianConstant.constantRootIsoOver k p hp.pos hbase f
    let : Subsingleton (Sheaf.H.{e} (mu X p) q) :=
      Curves.roots_subsingleton_H_of_curve k X f hdim p hp.pos hu htarget q hq
    exact (cohomologyMapIso_bijective rootIso q).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
