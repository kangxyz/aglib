/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlyingCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.Comparisons

/-!
# Whole composition coherence of the original underlying lower shriek

The original inverse-image comparison already respects composition. Its actual mate gives
composition of the original lower-shriek comparison, before any coefficient or Ext degree is
evaluated. All geometric suppliers of the mate equation are proved in the imported leaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {V U X : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ U) [Etale j] [Etale i]
  (Λ : Type (u + 1)) [Ring Λ]

omit [Etale j] [Etale i] in
private theorem moduleInverseImageUnderlyingIso_comp_hom (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing V Λ)).map
        ((moduleInverseImageCompIso Λ j i).hom.app M) ≫
      (moduleInverseImageUnderlyingIso Λ i).hom.app ((moduleInverseImage j Λ).obj M) ≫
      (inverseImage i).map ((moduleInverseImageUnderlyingIso Λ j).hom.app M) =
    (moduleInverseImageUnderlyingIso Λ (i ≫ j)).hom.app M ≫
      (inverseImageComp j i).hom.app ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) := by
  have h := hom_square_of_inv ((moduleInverseImageUnderlyingIso Λ (i ≫ j)).app M)
    (((moduleInverseImageUnderlyingIso Λ i).app ((moduleInverseImage j Λ).obj M)) ≪≫
      (inverseImage i).mapIso ((moduleInverseImageUnderlyingIso Λ j).app M))
    ((SheafOfModules.toSheaf (constantRing V Λ)).map
      ((moduleInverseImageCompIso Λ j i).hom.app M))
    ((inverseImageComp j i).hom.app ((SheafOfModules.toSheaf (constantRing X Λ)).obj M)) (by
      simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using
        moduleInverseImageUnderlyingIso_inv_comp Λ j i M)
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using h

/-- The original lower-shriek composition commutes with forgetting as a whole iso chain. -/
theorem moduleLowerShriekUnderlyingIso_comp :
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf (constantRing V Λ))
        (etaleLowerShriekCompIso j i) ≪≫
      (Functor.associator (SheafOfModules.toSheaf (constantRing V Λ))
        (etaleLowerShriek i) (etaleLowerShriek j)).symm ≪≫
      Functor.isoWhiskerRight (moduleLowerShriekUnderlyingIso i Λ).symm (etaleLowerShriek j) ≪≫
      Functor.associator (moduleLowerShriek i Λ)
        (SheafOfModules.toSheaf (constantRing U Λ)) (etaleLowerShriek j) ≪≫
      Functor.isoWhiskerLeft (moduleLowerShriek i Λ) (moduleLowerShriekUnderlyingIso j Λ).symm ≪≫
      (Functor.associator (moduleLowerShriek i Λ) (moduleLowerShriek j Λ)
        (SheafOfModules.toSheaf (constantRing X Λ))).symm =
    (moduleLowerShriekUnderlyingIso (i ≫ j) Λ).symm ≪≫
      Functor.isoWhiskerRight (moduleLowerShriekCompIso Λ j i)
        (SheafOfModules.toSheaf (constantRing X Λ)) := by
  apply Functor.underlying_comp_iso
  intro M
  exact scalarComparison_comp
    (moduleLowerShriekAdjunction i Λ) (etaleLowerShriekAdjunction i)
    (moduleLowerShriekAdjunction j Λ) (etaleLowerShriekAdjunction j)
    (moduleLowerShriekAdjunction (i ≫ j) Λ) (etaleLowerShriekAdjunction (i ≫ j))
    (moduleLowerShriekUnderlyingIso i Λ) (moduleLowerShriekUnderlyingIso j Λ)
    (moduleLowerShriekUnderlyingIso (i ≫ j) Λ)
    (moduleInverseImageUnderlyingIso Λ i) (moduleInverseImageUnderlyingIso Λ j)
    (moduleInverseImageUnderlyingIso Λ (i ≫ j))
    (moduleLowerShriekCompIso Λ j i) (etaleLowerShriekCompIso j i)
    (moduleInverseImageCompIso Λ j i) (inverseImageComp j i)
    (by
      apply TwoSquare.ext
      intro N
      exact congr_app (mate_moduleLowerShriekUnderlyingIso_inv i Λ) N)
    (by
      apply TwoSquare.ext
      intro N
      exact congr_app (mate_moduleLowerShriekUnderlyingIso_inv j Λ) N)
    (by
      apply TwoSquare.ext
      intro N
      exact congr_app (mate_moduleLowerShriekUnderlyingIso_inv (i ≫ j) Λ) N)
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
      (moduleLowerShriekAdjunction (i ≫ j) Λ)
      ((moduleLowerShriekAdjunction i Λ).comp (moduleLowerShriekAdjunction j Λ))
      (moduleInverseImageCompIso Λ j i))
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
      (etaleLowerShriekAdjunction (i ≫ j))
      ((etaleLowerShriekAdjunction i).comp (etaleLowerShriekAdjunction j))
      (inverseImageComp j i))
    (moduleInverseImageUnderlyingIso_comp_hom j i Λ) M
/-- The forward component equation evaluates the same original whole composition square. -/
theorem moduleLowerShriekUnderlyingIso_comp_hom_app (M : ModuleSheaf V Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleLowerShriekCompIso Λ j i).hom.app M) ≫
      (moduleLowerShriekUnderlyingIso j Λ).hom.app ((moduleLowerShriek i Λ).obj M) ≫
      (etaleLowerShriek j).map ((moduleLowerShriekUnderlyingIso i Λ).hom.app M) =
    (moduleLowerShriekUnderlyingIso (i ≫ j) Λ).hom.app M ≫
      (etaleLowerShriekCompIso j i).hom.app
        ((SheafOfModules.toSheaf (constantRing V Λ)).obj M) :=
  Functor.underlying_comp_hom_app (moduleLowerShriekUnderlyingIso i Λ)
    (moduleLowerShriekUnderlyingIso j Λ) (moduleLowerShriekUnderlyingIso (i ≫ j) Λ)
    (moduleLowerShriekCompIso Λ j i) (etaleLowerShriekCompIso j i)
    (moduleLowerShriekUnderlyingIso_comp j i Λ) M

end AlgebraicGeometry.Scheme.EtaleCohomology
