/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunctionCompatibility

/-! # The original chart exchange under the coefficient equivalence -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]
  (Λ : Type (u + 1)) [Ring Λ]

/-- The original chart exchange has its whole defining comparison value. -/
theorem moduleEtaleBaseChangeIso_valued_whole :
    Functor.whiskerRight (moduleEtaleBaseChangeIso f g Λ).hom
        (moduleSheafEquivalence T Λ).inverse ≫ (moduleEtaleBaseChangeRightIso f g Λ).hom =
      (moduleEtaleBaseChangeLeftIso f g Λ).hom ≫
        Functor.whiskerLeft (moduleSheafEquivalence X Λ).inverse
          (moduleValuedEtaleBaseChangeIso f g Λ).hom :=
  ValuedComparison.exchangeIso_hom_comparison (moduleSheafEquivalence T Λ).inverse
    (moduleEtaleBaseChangeLeftIso f g Λ) (moduleEtaleBaseChangeRightIso f g Λ)
    (moduleValuedEtaleBaseChangeIso f g Λ)

/-- The actual native chart exchange satisfies its defining valued comparison square. -/
@[reassoc]
theorem moduleEtaleBaseChangeIso_valued (M : ModuleSheaf X Λ) :
    (moduleSheafEquivalence T Λ).inverse.map
        ((moduleEtaleBaseChangeIso f g Λ).hom.app M) ≫
      (moduleDirectImageComparison (pullback.fst g f) Λ).hom.app
        ((moduleInverseImage (pullback.snd g f) Λ).obj M) ≫
      (moduleValuedDirectImage (pullback.fst g f) Λ).map
        ((moduleInverseImageValuedIso Λ (pullback.snd g f)).hom.app M) =
    (moduleInverseImageValuedIso Λ g).hom.app ((moduleDirectImage f Λ).obj M) ≫
      (moduleValuedInverseImage g Λ).map ((moduleDirectImageComparison f Λ).hom.app M) ≫
      (moduleValuedEtaleBaseChangeIso f g Λ).hom.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) := by
  have h := NatTrans.congr_app (moduleEtaleBaseChangeIso_valued_whole f g Λ) M
  simpa only [moduleEtaleBaseChangeRightIso, moduleEtaleBaseChangeLeftIso,
    scalarMateSourceIso, scalarMateTargetIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Category.assoc] using h

end AlgebraicGeometry.Scheme.EtaleCohomology
