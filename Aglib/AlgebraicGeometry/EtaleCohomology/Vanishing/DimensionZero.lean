/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.ZeroFinite
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.StrictlyLocal.Standard

/-! # Proper zero-dimensional vanishing for arbitrary abelian coefficients

Proper morphisms with zero-dimensional ordinary fibres have zero positive
original higher direct images. Over a separably closed field, proper schemes
of dimension at most zero have zero positive original `Sheaf.H`. Neither result
requires torsion, constructibility, or proper base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u wX wS e

attribute [local instance] hasSheafifyLarge

/-- Positive original higher direct images vanish for a proper morphism whose
ordinary fibres have dimension at most zero. The coefficient is arbitrary, and
the source and target derived-category universes remain independent. -/
theorem isZero_higherDirectImage_obj_of_fiber_dimension_le_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 0)
    [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (hq : 0 < q) :
    IsZero ((higherDirectImage f q).obj F) := by
  let : IsFinite f := .of_isProper_of_fiber_topologicalKrullDim_le_zero f hdim
  exact Finite.isZero_higherDirectImage_obj_of_isFinite f F q hq

/-- A proper zero-dimensional scheme over a separably closed field has trivial
positive original cohomology for every abelian sheaf. The original Ext universe
is arbitrary; only the auxiliary field-site Ext universe is chosen internally. -/
theorem subsingleton_H_of_proper_dimension_le_zero
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{e} F q) := by
  let : IsFinite p := .of_isProper_of_topologicalKrullDim_le_zero p hdim
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} (Spec (.of k))) := HasExt.standard _
  let : HenselianLocalRing k := Field.henselian _
  let : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  let : Subsingleton (Sheaf.H.{u + 2} ((directImage p).obj F) q) :=
    StrictlyLocal.subsingleton_H_standard k ((directImage p).obj F) q hq
  exact (Finite.finiteCohomologyDirectImageAddEquiv.{u, e, u + 2} p F q).surjective.subsingleton

/-- Every positive original cohomology class of a proper zero-dimensional scheme
over a separably closed field is zero, for arbitrary abelian coefficients. -/
theorem H_eq_zero_of_proper_dimension_le_zero
    {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (hq : 0 < q)
    (a : Sheaf.H.{e} F q) : a = 0 := by
  let := subsingleton_H_of_proper_dimension_le_zero p hdim F q hq
  exact Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
