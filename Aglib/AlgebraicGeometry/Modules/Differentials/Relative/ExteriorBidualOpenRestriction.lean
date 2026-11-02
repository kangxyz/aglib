/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FormsFiniteType
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.CoherentOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Map


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / ExteriorBidualOpenRestriction

Source: `IntegralTrace/RawFormsOpenRestriction.lean`.
Incoming SHA256: `aa7df6ace0004643fe1b5c990839bc85b5932960760afba9ecf88716442284b0`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X U : Scheme.{u}} {Λ : CommRingCat.{u}}
  (a : X ⟶ Spec Λ) (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

variable [IsLocallyNoetherian X] {R : CommRingCat.{u}}

variable (hM : QuasiCoherent.affineLocallyFiniteType X
  (moduleExteriorPower X (relativeDifferentialSheaf a) n))

/-- The same global raw bidual supplies the actual affine local source map. -/
def bidualFormsAffineRestrictionMapOfCoherent (j : Spec R ⟶ X) [IsOpenImmersion j] :
    (show X.Modules from Invertible.dualSheaf X (Invertible.dualSheaf X
      (moduleExteriorPower X (relativeDifferentialSheaf a) n))).restrict j ⟶
    Invertible.dualSheaf (Spec R) (Invertible.dualSheaf (Spec R)
      (moduleExteriorPower (Spec R) (relativeDifferentialSheaf (j ≫ a)) n)) :=
  Invertible.coherentBidualOpenRestriction j _ hM ≫
    Invertible.doubleDualMap (Spec R) (rawFormsOpenIso a j n).hom
/-- Original evaluation is preserved on the original chart, including the raw arrow. -/
theorem bidualFormsAffineRestrictionMapOfCoherent_evaluation
    (j : Spec R ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).map (Invertible.bidualMap X
      (moduleExteriorPower X (relativeDifferentialSheaf a) n)) ≫
      bidualFormsAffineRestrictionMapOfCoherent a n hM j =
    (rawFormsOpenIso a j n).hom ≫ Invertible.bidualMap (Spec R)
      (moduleExteriorPower (Spec R) (relativeDifferentialSheaf (j ≫ a)) n) := by
  let r := (Scheme.Modules.restrictFunctor j).map (Invertible.bidualMap X
    (moduleExteriorPower X (relativeDifferentialSheaf a) n))
  let b := Invertible.coherentBidualOpenRestriction j _
    hM
  let d := Invertible.doubleDualMap (Spec R) (rawFormsOpenIso a j n).hom
  have h := Invertible.coherentBidualOpenRestriction_evaluation j _
    hM
  exact (Category.assoc r b d).symm.trans
    ((congrArg (fun t => t ≫ d) h).trans
      (Invertible.bidualMap_naturality (Spec R) (rawFormsOpenIso a j n).hom))
/-- The original finite-type interface supplies coherence to the same restriction map. -/
def bidualFormsAffineRestrictionMap [LocallyOfFiniteType a]
    (j : Spec R ⟶ X) [IsOpenImmersion j] :
    (show X.Modules from Invertible.dualSheaf X (Invertible.dualSheaf X
      (moduleExteriorPower X (relativeDifferentialSheaf a) n))).restrict j ⟶
    Invertible.dualSheaf (Spec R) (Invertible.dualSheaf (Spec R)
      (moduleExteriorPower (Spec R) (relativeDifferentialSheaf (j ≫ a)) n)) :=
  bidualFormsAffineRestrictionMapOfCoherent a n (rawForms_affineLocallyFiniteType a n) j
/-- The old finite-type evaluation law is the same coherent evaluation law. -/
theorem bidualFormsAffineRestrictionMap_evaluation [LocallyOfFiniteType a]
    (j : Spec R ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).map (Invertible.bidualMap X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n)) ≫
      bidualFormsAffineRestrictionMap a n j =
    (rawFormsOpenIso a j n).hom ≫ Invertible.bidualMap (Spec R)
      (moduleExteriorPower (Spec R) (relativeDifferentialSheaf (j ≫ a)) n) :=
  bidualFormsAffineRestrictionMapOfCoherent_evaluation a n
    (rawForms_affineLocallyFiniteType a n) j

end AlgebraicGeometry.Scheme.Modules.Differentials
