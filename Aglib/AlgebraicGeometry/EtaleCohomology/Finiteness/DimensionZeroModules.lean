/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.DimensionZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.DimensionZero

/-! # All-degree original module finiteness in proper dimension zero

The genuine constructible module H0 theorem and the existing positive-degree
vanishing theorem have complementary roles. Together they give finite original
cohomology in every degree over any commutative coefficient ring. The H0 group
need not be finite as a set; positive groups are actually zero.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r e
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Positive original module cohomology is zero in proper dimension zero,
without any constructibility or torsion assumption on the coefficient. -/
theorem moduleCohomology_subsingleton_of_proper_dimension_le_zero
    (R : Type r) [CommRing R] {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : ModuleSheaf R X) (q : ℕ) (hq : 0 < q) :
    Subsingleton
      ((ModuleCat.Sheaf.cohomology.{u + 1, u, r, e} X.smallEtaleTopology R q).obj F) :=
  Vanishing.subsingleton_H_of_proper_dimension_le_zero p hdim
    ((moduleUnderlying R X).obj F) q hq

/-- Every original cohomology module of a constructible coefficient on a proper
zero-dimensional geometric scheme is finite over its original ring. No
Noetherianity, torsion, reducedness or finite underlying coefficient set is used. -/
theorem moduleCohomology_finite_of_proper_dimension_le_zero
    (R : Type r) [CommRing R] {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    {F : ModuleSheaf R X} (hF : IsConstructible F) (q : ℕ) :
    Module.Finite R
      ((ModuleCat.Sheaf.cohomology.{u + 1, u, r, e} X.smallEtaleTopology R q).obj F) := by
  cases q with
  | zero => exact moduleH0_finite_of_proper_dimension_le_zero R p hdim hF
  | succ q =>
    let : Subsingleton
        ((ModuleCat.Sheaf.cohomology.{u + 1, u, r, e} X.smallEtaleTopology R (q + 1)).obj F) :=
      moduleCohomology_subsingleton_of_proper_dimension_le_zero R p hdim F (q + 1)
        (Nat.zero_lt_succ q)
    infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Finiteness
