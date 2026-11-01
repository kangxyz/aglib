/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.PullbackPartition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ZModComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.PullbackLocality

/-! # Original abelian partitions and pullback on a qcqs base

A genuine positive ZMod lift and the existing module finite-open gluing
producer supply a global partition. Forgetting this finite coefficient ring
retains the same original strata and maps. The existing original abelian
partition pullback then applies; no new site or coefficient model is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- Actual qcqs constructibility supplies a global original abelian partition,
using a positive finite coefficient ring and the existing module producer. -/
theorem nonempty_constructiblePartition_of_qcqs
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsConstructible F) :
    Nonempty (ConstructiblePartition F) := by
  obtain ⟨n, hn, M, hM, ⟨e⟩⟩ := Modules.exists_constructible_zmodSheaf F hF
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨t⟩ := Modules.nonempty_constructiblePartition hM
  exact ⟨t.underlying.ofIso e⟩

/-- Original inverse image along any scheme morphism preserves constructible
abelian coefficients when the original target is qcqs. -/
theorem isConstructible_pullback_of_qcqs
    {X S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : S ⟶ X) {F : AbelianSheaf.{u, u + 1} X} (hF : IsConstructible F) :
    IsConstructible ((inverseImage f).obj F) := by
  obtain ⟨t⟩ := nonempty_constructiblePartition_of_qcqs hF
  exact isConstructible_pullback_of_partition f t

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
