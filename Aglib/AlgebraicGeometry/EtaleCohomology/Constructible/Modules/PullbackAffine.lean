/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Constructible module inverse image over an affine base

Actual constructible partitions pull back along quasi-compact morphisms from
quasi-separated schemes over a compact base. Their module restrictions are
transported by the native inverse-image composition isomorphisms on the literal
cartesian squares. Consequently a module coefficient carrying a global
partition on a qcqs base has constructible inverse image along every scheme
morphism. Affine-local constructibility supplies the needed partition when
the target is affine; the source and the original morphism are unrestricted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Pull back the original actual partition and its finite-type module
restrictions. Compactness and quasi-compactness are the hypotheses of the
coefficient-independent geometric partition construction. -/
def ConstructiblePartition.baseChange {X S : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace S] {F : ModuleSheaf R X}
    (t : ConstructiblePartition F) (f : S ⟶ X) [QuasiCompact f] :
    ConstructiblePartition ((moduleInverseImage R f).obj F) where
  toFiniteLocallyClosedPartition := t.toFiniteLocallyClosedPartition.baseChange f
  locally_constant i := by
    let a := pullback.fst (t.inclusion i) f
    let b := pullback.snd (t.inclusion i) f
    let e : (moduleInverseImage R b).obj ((moduleInverseImage R f).obj F) ≅
        (moduleInverseImage R a).obj ((moduleInverseImage R (t.inclusion i)).obj F) :=
      ((moduleInverseImageComp R f b).app F).symm ≪≫
        eqToIso (congrArg (fun g => (moduleInverseImage R g).obj F)
          (pullback.condition (f := t.inclusion i) (g := f)).symm) ≪≫
        (moduleInverseImageComp R (t.inclusion i) a).app F
    exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr
      (isFiniteTypeLocallyConstant_pullback a (t.locally_constant i))

/-- A global actual partition on a qcqs target gives affine-local
constructibility after any original scheme inverse image. No quasi-compactness
of the original morphism or source is assumed. -/
theorem isConstructible_pullback_of_partition {X S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {F : ModuleSheaf R X}
    (f : S ⟶ X) (t : ConstructiblePartition F) :
    IsConstructible ((moduleInverseImage R f).obj F) := by
  intro U
  have : IsAffine U.1.toScheme := U.property
  exact ⟨(t.baseChange (U.1.ι ≫ f)).ofIso ((moduleInverseImageComp R f U.1.ι).app F)⟩

/-- Actual constructible module inverse image along an arbitrary morphism
with affine target. Only affine source tests are made quasi-compact; no such
hypothesis is imposed on the original morphism. -/
theorem isConstructible_pullback_of_isAffine {X S : Scheme.{u}} [IsAffine X]
    (f : S ⟶ X) {F : ModuleSheaf R X} (hF : IsConstructible F) :
    IsConstructible ((moduleInverseImage R f).obj F) := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have : IsAffine U.1.toScheme := U.property
  obtain ⟨t⟩ := hF U
  let g : S ⟶ U.1.toScheme := f ≫ X.topIso.inv
  have hg : g ≫ U.1.ι = f := by
    change (f ≫ X.topIso.inv) ≫ X.topIso.hom = f
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let e : (moduleInverseImage R g).obj ((moduleInverseImage R U.1.ι).obj F) ≅
      (moduleInverseImage R f).obj F :=
    ((moduleInverseImageComp R U.1.ι g).app F).symm ≪≫
      eqToIso (congrArg (fun k => (moduleInverseImage R k).obj F) hg)
  exact (isConstructible_iff_of_iso e).mp (isConstructible_pullback_of_partition g t)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
