/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Affine

/-! # Ambient finite presentation on original affine charts

Finite presentation after restriction to the actual affine-open inclusions
also holds after any open immersion from a spectrum. The original open map
factors through its actual open image by the canonical scheme isomorphism.
Its inverse-image equivalence and the original composition comparison supply
the transport. No general inverse-image preservation of FP is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

/-- Affine-open-inclusion FP gives FP on every original open spectrum chart,
through its canonical isomorphism with the actual affine open image. -/
theorem affineRestriction_isFinitelyPresentable_spec_open
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (hF : ∀ V : X.affineOpens, IsFinitelyPresentable.{u + 1}
      ((inverseImage V.1.ι).obj F))
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j] :
    IsFinitelyPresentable.{u + 1} ((inverseImage j).obj F) := by
  let e := j.isoOpensRange
  have hV : IsAffine j.opensRange.toScheme := IsAffine.of_isIso e.inv
  let V : X.affineOpens := ⟨j.opensRange, hV⟩
  have : IsFinitelyPresentable.{u + 1} ((inverseImage j.opensRange.ι).obj F) := hF V
  have : (inverseImage e.hom).IsEquivalence :=
    (inverseImageEquivalenceOfIso e).isEquivalence_functor
  let eF : (inverseImage j).obj F ≅
      (inverseImage e.hom).obj ((inverseImage j.opensRange.ι).obj F) :=
    eqToIso (congrArg (fun f : Spec R ⟶ X => (inverseImage f).obj F)
      j.isoOpensRange_hom_ι.symm) ≪≫
        (inverseImageComp j.opensRange.ι e.hom).app F
  let P : ObjectProperty (AbelianSheaf.{u, u + 1} (Spec R)) :=
    isCardinalPresentable.{u + 1, u + 1, u + 2}
      (AbelianSheaf.{u, u + 1} (Spec R)) Cardinal.aleph0.{u + 1}
  have hP : P ((inverseImage e.hom).obj ((inverseImage j.opensRange.ι).obj F)) :=
    (inferInstance : IsFinitelyPresentable.{u + 1}
      ((inverseImage e.hom).obj ((inverseImage j.opensRange.ι).obj F)))
  exact P.prop_of_iso eF.symm hP

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
