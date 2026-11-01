/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionCoherence
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageIdentityCoherence

/-! # The original source unit law on native torsion inverse images -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
private theorem fullSubcategory_eqToHom_hom
    {C : Type*} [Category* C] (P : ObjectProperty C)
    {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg (fun Z : P.FullSubcategory => Z.obj) h) := by
  cases h
  rfl

universe u wX wS
variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}} (f : S ⟶ X)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

private theorem torsionId_hom_app
    (K : (moduleTorsionCohomologyPlus S Λ).FullSubcategory) :
    ((moduleDerivedInverseImageTorsionIdIso Λ S).hom.app K).hom =
      (moduleDerivedInverseImageIdIso Λ S).hom.app K.obj := by
  change (moduleDerivedInverseImageIdIso Λ S).hom.app K.obj ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The native torsion compositor retains the unchanged original source identity law. -/
theorem moduleDerivedInverseImageTorsionCompIso_comp_id :
    moduleDerivedInverseImageTorsionCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion f Λ)
          (moduleDerivedInverseImageTorsionIdIso Λ S) ≪≫
        Functor.rightUnitor (moduleDerivedInverseImageTorsion f Λ) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleDerivedInverseImageTorsion k Λ)
        (Category.id_comp f)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  have h := congrArg (fun i => i.hom.app K.obj)
    (moduleDerivedInverseImageCompIso_comp_id Λ f)
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    moduleDerivedInverseImageTorsionCompIso_hom_app, torsionId_hom_app,
    eqToIso.hom, eqToHom_app, fullSubcategory_eqToHom_hom] at h ⊢
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology
