/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.PullbackPartition

/-! # Original constructible abelian inverse image from an affine target

The original affine-local definition supplies a partition on the top affine
open. Its actual inverse image along the original map, factored through the
canonical top-open isomorphism, is constructible. Neither the original source
nor the original map is assumed quasi-compact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

/-- Constructibility pulls back along any original morphism with affine target. -/
theorem isConstructible_pullback_of_isAffine {X S : Scheme.{u}} [IsAffine X]
    (f : S ⟶ X) {F : AbelianSheaf.{u, u + 1} X} (hF : IsConstructible F) :
    IsConstructible ((inverseImage f).obj F) := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have : IsAffine U.1.toScheme := U.property
  obtain ⟨t⟩ := hF U
  let g : S ⟶ U.1.toScheme := f ≫ X.topIso.inv
  have hg : g ≫ U.1.ι = f := by
    change (f ≫ X.topIso.inv) ≫ X.topIso.hom = f
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let e : (inverseImage g).obj ((inverseImage U.1.ι).obj F) ≅
      (inverseImage f).obj F :=
    ((inverseImageComp U.1.ι g).app F).symm ≪≫
      eqToIso (congrArg (fun k => (inverseImage k).obj F) hg)
  exact (isConstructible_iff_of_iso e).mp (isConstructible_pullback_of_partition g t)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
