/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.BaseChange

/-! # Original abelian constructible partitions under inverse image

The coefficient-independent geometric partition pulls back along the original
scheme morphism. The literal cartesian square and original inverse-image
composition isomorphisms transport finite local constancy. A global partition
on a qcqs target therefore yields affine-local constructibility after any
inverse image; the original map need not be quasi-compact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- Pull back the actual abelian coefficient partition using the original
scheme fibre products and original coefficient comparison isomorphisms. -/
def ConstructiblePartition.baseChange {X S : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace S] {F : AbelianSheaf.{u, u + 1} X}
    (t : ConstructiblePartition F) (f : S ⟶ X) [QuasiCompact f] :
    ConstructiblePartition ((inverseImage f).obj F) where
  toFiniteLocallyClosedPartition := t.toFiniteLocallyClosedPartition.baseChange f
  locally_constant i := by
    let a := pullback.fst (t.inclusion i) f
    let b := pullback.snd (t.inclusion i) f
    let e : (inverseImage b).obj ((inverseImage f).obj F) ≅
        (inverseImage a).obj ((inverseImage (t.inclusion i)).obj F) :=
      ((inverseImageComp f b).app F).symm ≪≫
        eqToIso (congrArg (fun g => (inverseImage g).obj F)
          (pullback.condition (f := t.inclusion i) (g := f)).symm) ≪≫
        (inverseImageComp (t.inclusion i) a).app F
    exact (isFiniteLocallyConstant_iff_of_iso e).mpr
      (isFiniteLocallyConstant_pullback a (t.locally_constant i))

/-- A global genuine partition on a qcqs target gives constructible original
inverse image along any scheme morphism. Only affine source tests need be qcqs. -/
theorem isConstructible_pullback_of_partition {X S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {F : AbelianSheaf.{u, u + 1} X}
    (f : S ⟶ X) (t : ConstructiblePartition F) :
    IsConstructible ((inverseImage f).obj F) := by
  intro U
  have : IsAffine U.1.toScheme := U.property
  exact ⟨(t.baseChange (U.1.ι ≫ f)).ofIso ((inverseImageComp f U.1.ι).app F)⟩

/-- A genuine global constructible partition on a qcqs scheme satisfies the
original affine-local constructibility predicate. -/
theorem isConstructible_of_partition {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {F : AbelianSheaf.{u, u + 1} X}
    (t : ConstructiblePartition F) : IsConstructible F :=
  (isConstructible_iff_of_iso ((inverseImageId X).app F)).mp
    (isConstructible_pullback_of_partition (𝟙 X) t)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
