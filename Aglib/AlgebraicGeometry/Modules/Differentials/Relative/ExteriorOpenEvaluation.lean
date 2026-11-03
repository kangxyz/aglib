/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorBidualOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FormsFiniteType


/-!
# Original affine evaluation followed by an original raw arrow

Compose the accepted restriction-evaluation square with original bidual
naturality before specializing its module carriers to a blowup chart.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- Original affine restriction followed by an original raw arrow preserves evaluation. -/
theorem bidualFormsAffineRestrictionMapOfCoherent_comp_evaluation
    {X : Scheme.{u}} [IsLocallyNoetherian X] {Λ R : CommRingCat.{u}}
    (a : X ⟶ Spec Λ)
    (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (hM : QuasiCoherent.affineLocallyFiniteType X
      (moduleExteriorPower X (relativeDifferentialSheaf a) n))
    (F : (Spec R).Modules)
    (e : moduleExteriorPower (Spec R) (relativeDifferentialSheaf (j ≫ a)) n ⟶ F) :
    (Scheme.Modules.restrictFunctor j).map (Invertible.bidualMap X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n)) ≫
        (bidualFormsAffineRestrictionMapOfCoherent a n hM j ≫ Invertible.doubleDualMap (Spec R) e) =
      ((rawFormsOpenIso a j n).hom ≫ e) ≫ Invertible.bidualMap (Spec R) F := by
  let r := (Scheme.Modules.restrictFunctor j).map (Invertible.bidualMap X
    (moduleExteriorPower X (relativeDifferentialSheaf a) n))
  let b := bidualFormsAffineRestrictionMapOfCoherent a n hM j
  let d := Invertible.doubleDualMap (Spec R) e
  have h := bidualFormsAffineRestrictionMapOfCoherent_evaluation a n hM j
  have h' := Invertible.bidualMap_naturality (Spec R) e
  exact (Category.assoc r b d).symm.trans
    ((congrArg (fun t => t ≫ d) h).trans
      ((Category.assoc (rawFormsOpenIso a j n).hom _ d).trans
        ((congrArg (fun t => (rawFormsOpenIso a j n).hom ≫ t) h').trans
          (Category.assoc (rawFormsOpenIso a j n).hom e _).symm)))

/-- The original finite-type law supplies its existing coherence proof. -/
theorem bidualFormsAffineRestrictionMap_comp_evaluation
    {X : Scheme.{u}} [IsLocallyNoetherian X] {Λ R : CommRingCat.{u}}
    (a : X ⟶ Spec Λ) [LocallyOfFiniteType a]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (F : (Spec R).Modules)
    (e : moduleExteriorPower (Spec R) (relativeDifferentialSheaf (j ≫ a)) n ⟶ F) :
    (Scheme.Modules.restrictFunctor j).map (Invertible.bidualMap X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n)) ≫
        (bidualFormsAffineRestrictionMap a n j ≫ Invertible.doubleDualMap (Spec R) e) =
      ((rawFormsOpenIso a j n).hom ≫ e) ≫ Invertible.bidualMap (Spec R) F :=
  bidualFormsAffineRestrictionMapOfCoherent_comp_evaluation a j n
    (rawForms_affineLocallyFiniteType a n) F e

end AlgebraicGeometry.Scheme.Modules.Differentials
