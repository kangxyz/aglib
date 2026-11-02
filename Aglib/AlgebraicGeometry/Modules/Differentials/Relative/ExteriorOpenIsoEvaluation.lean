/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorBidualOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenEvaluation
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FormsFiniteType


/-!
# Evaluation with the original whole raw source isomorphism retained

The same raw and bidual composites are retained at variable schemes before
specializing the original chart congruence. No alternative map is defined.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- Retain the original raw source isomorphism and original bidual composite
before evaluating the original chart congruence. -/
theorem bidualFormsAffineRestrictionMapOfCoherent_iso_evaluation
    {X : Scheme.{u}} [IsLocallyNoetherian X] {Λ R : CommRingCat.{u}}
    (a : X ⟶ Spec Λ)
    (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (hM : QuasiCoherent.affineLocallyFiniteType X
      (moduleExteriorPower X (relativeDifferentialSheaf a) n))
    (F : (Spec R).Modules)
    (e : moduleExteriorPower (Spec R) (relativeDifferentialSheaf (j ≫ a)) n ≅ F) :
    let r : (moduleExteriorPower X (relativeDifferentialSheaf a) n).restrict j ≅ F :=
      rawFormsOpenIso a j n ≪≫ e
    let b : (show X.Modules from Invertible.dualSheaf X (Invertible.dualSheaf X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n))).restrict j ⟶
        Invertible.dualSheaf (Spec R) (Invertible.dualSheaf (Spec R) F) :=
      bidualFormsAffineRestrictionMapOfCoherent a n hM j ≫ Invertible.doubleDualMap (Spec R) e.hom
    (Scheme.Modules.restrictFunctor j).map (Invertible.bidualMap X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n)) ≫ b =
      r.hom ≫ Invertible.bidualMap (Spec R) F := by
  intro r b
  simpa only [r, b, Iso.trans_hom, Scheme.Modules.restrict] using
    (bidualFormsAffineRestrictionMapOfCoherent_comp_evaluation a j n hM F e.hom)

/-- The original finite-type law supplies its existing coherence proof. -/
theorem bidualFormsAffineRestrictionMap_iso_evaluation
    {X : Scheme.{u}} [IsLocallyNoetherian X] {Λ R : CommRingCat.{u}}
    (a : X ⟶ Spec Λ) [LocallyOfFiniteType a]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (F : (Spec R).Modules)
    (e : moduleExteriorPower (Spec R) (relativeDifferentialSheaf (j ≫ a)) n ≅ F) :
    let r : (moduleExteriorPower X (relativeDifferentialSheaf a) n).restrict j ≅ F :=
      rawFormsOpenIso a j n ≪≫ e
    let b : (show X.Modules from Invertible.dualSheaf X (Invertible.dualSheaf X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n))).restrict j ⟶
        Invertible.dualSheaf (Spec R) (Invertible.dualSheaf (Spec R) F) :=
      bidualFormsAffineRestrictionMap a n j ≫ Invertible.doubleDualMap (Spec R) e.hom
    (Scheme.Modules.restrictFunctor j).map (Invertible.bidualMap X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n)) ≫ b =
      r.hom ≫ Invertible.bidualMap (Spec R) F :=
  bidualFormsAffineRestrictionMapOfCoherent_iso_evaluation a j n
    (rawForms_affineLocallyFiniteType a n) F e

end AlgebraicGeometry.Scheme.Modules.Differentials
