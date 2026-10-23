/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.StructureSheaf.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLift

/-! # Restriction of the original structure coefficient to the Zariski site

The comparison uses the native open-subscheme global-section isomorphism.
Neither the étale structure coefficient nor the Zariski coefficient is replaced.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- The original ring sections on open étale charts are the original Zariski ring sections. -/
def zariskiStructurePresheafIso (X : Scheme.{u}) :
    (opensToEtale X).op ⋙ structurePresheaf X ≅ X.presheaf :=
  by
    let e : (opensToEtale X).op ⋙ (Scheme.Etale.forget X).op ≅ X.restrictFunctor.op :=
      (Functor.opComp (opensToEtale X) (Scheme.Etale.forget X)).symm ≪≫
        NatIso.op (opensToEtaleForgetIso X).symm
    change (opensToEtale X).op ⋙ (Scheme.Etale.forget X).op ⋙
      (Over.forget X).op ⋙ Scheme.Γ ≅ X.presheaf
    exact (Functor.associator (opensToEtale X).op (Scheme.Etale.forget X).op
      ((Over.forget X).op ⋙ Scheme.Γ)).symm ≪≫
      Functor.isoWhiskerRight e ((Over.forget X).op ⋙ Scheme.Γ) ≪≫ X.restrictFunctorΓ

/-- The original additive étale structure coefficient restricts to the literal
value lift of the original Zariski structure sheaf. -/
def zariskiStructureIso (X : Scheme.{u}) :
    (zariskiRestriction X).obj (additiveStructureSheaf X) ≅
      (Sheaf.BasisAcyclicity.valueLift.{u,u,u,u+1}
        (Opens.grothendieckTopology X)).obj (Scheme.structureAddSheaf X) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight (zariskiStructurePresheafIso X)
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u+1,u}))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
