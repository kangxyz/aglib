/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekCompositionConjugacy
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekIdentityConjugacy
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionModel

/-! # Original unbounded lower-shriek associativity and units

The equations are transported through the actual adjunction conjugacy from the
original inverse-image coherence, with independent derived models at every vertex.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wT wV
variable (Λ : Type (u + 1)) [Ring Λ]

/-- Equality transport has the reversed original inverse-image mate. -/
theorem conjugateEquiv_moduleUnboundedDerivedLowerShriek_eqToHom {X S : Scheme.{u}}
    {f g : S ⟶ X} [Etale f] [Etale g] (h : f = g)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    conjugateEquiv (moduleUnboundedDerivedLowerShriekAdjunction g Λ)
      (moduleUnboundedDerivedLowerShriekAdjunction f Λ)
      (eqToHom (moduleUnboundedDerivedLowerShriek_congr Λ h)) =
      eqToHom (congrArg (fun k : S ⟶ X => moduleUnboundedDerivedInverseImage Λ k) h.symm) := by
  subst g
  simp

/-- The exact original lower-shriek compositors associate. -/
theorem moduleUnboundedDerivedLowerShriekCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) [Etale f] [Etale g] [Etale h]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)] :
    moduleUnboundedDerivedLowerShriekCompIso Λ (g ≫ f) h ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedLowerShriek h Λ)
          (moduleUnboundedDerivedLowerShriekCompIso Λ f g) =
      eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ (Category.assoc h g f).symm) ≪≫
        moduleUnboundedDerivedLowerShriekCompIso Λ f (h ≫ g) ≪≫
        Functor.isoWhiskerRight (moduleUnboundedDerivedLowerShriekCompIso Λ g h)
          (moduleUnboundedDerivedLowerShriek f Λ) ≪≫
        Functor.associator (moduleUnboundedDerivedLowerShriek h Λ)
          (moduleUnboundedDerivedLowerShriek g Λ) (moduleUnboundedDerivedLowerShriek f Λ) := by
  let af := moduleUnboundedDerivedLowerShriekAdjunction f Λ
  let ag := moduleUnboundedDerivedLowerShriekAdjunction g Λ
  let ah := moduleUnboundedDerivedLowerShriekAdjunction h Λ
  let afg := moduleUnboundedDerivedLowerShriekAdjunction (g ≫ f) Λ
  let agh := moduleUnboundedDerivedLowerShriekAdjunction (h ≫ g) Λ
  let adjTotal :=  moduleUnboundedDerivedLowerShriekAdjunction (h ≫ (g ≫ f)) Λ
  let adjTotalAssoc :=  moduleUnboundedDerivedLowerShriekAdjunction ((h ≫ g) ≫ f) Λ
  have hL : conjugateEquiv (ah.comp (ag.comp af)) adjTotal
      ((moduleUnboundedDerivedLowerShriekCompIso Λ (g ≫ f) h).hom ≫
        Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek h Λ)
          (moduleUnboundedDerivedLowerShriekCompIso Λ f g).hom) =
      Functor.whiskerRight (moduleUnboundedDerivedInverseImageCompIso Λ f g).inv
        (moduleUnboundedDerivedInverseImage Λ h) ≫
        (moduleUnboundedDerivedInverseImageCompIso Λ (g ≫ f) h).inv := by
    rw [← conjugateEquiv_comp _ (ah.comp afg), conjugateEquiv_whiskerLeft,
      conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom,
      conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom]
  have hR : conjugateEquiv (ah.comp (ag.comp af)) adjTotal
      (eqToHom (moduleUnboundedDerivedLowerShriek_congr Λ (Category.assoc h g f).symm) ≫
        (moduleUnboundedDerivedLowerShriekCompIso Λ f (h ≫ g)).hom ≫
        Functor.whiskerRight (moduleUnboundedDerivedLowerShriekCompIso Λ g h).hom
          (moduleUnboundedDerivedLowerShriek f Λ) ≫
        (Functor.associator (moduleUnboundedDerivedLowerShriek h Λ)
          (moduleUnboundedDerivedLowerShriek g Λ) (moduleUnboundedDerivedLowerShriek f Λ)).hom) =
      (Functor.associator (moduleUnboundedDerivedInverseImage Λ f)
        (moduleUnboundedDerivedInverseImage Λ g) (moduleUnboundedDerivedInverseImage Λ h)).hom ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ f)
          (moduleUnboundedDerivedInverseImageCompIso Λ g h).inv ≫
        (moduleUnboundedDerivedInverseImageCompIso Λ f (h ≫ g)).inv ≫
        eqToHom (congrArg (fun k : V ⟶ X => moduleUnboundedDerivedInverseImage Λ k)
          (Category.assoc h g f)) := by
    rw [← conjugateEquiv_comp _ adjTotalAssoc, ← conjugateEquiv_comp _ (agh.comp af),
      ← conjugateEquiv_comp _ ((ah.comp ag).comp af),
      conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
      conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom,
      conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom,
      conjugateEquiv_moduleUnboundedDerivedLowerShriek_eqToHom]
    all_goals simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv (ah.comp (ag.comp af)) adjTotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    eqToIso.hom]
  rw [hL, hR]
  apply NatTrans.ext
  funext M
  have hi := congrArg (fun e => e.inv.app M) (moduleUnboundedDerivedInverseImageCompIso_assoc Λ f g
    h)
  have hi' := congrArg (fun t => t ≫ eqToHom
    (congrArg (fun k : V ⟶ X => (moduleUnboundedDerivedInverseImage Λ k).obj M)
      (Category.assoc h g f))) hi.symm
  simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    eqToIso.inv, eqToHom_app, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using hi'

/-- The native lower-shriek comparison with the source identity is normalized. -/
theorem moduleUnboundedDerivedLowerShriekCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleUnboundedDerivedLowerShriekCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerRight (moduleUnboundedDerivedLowerShriekIdIso Λ S)
          (moduleUnboundedDerivedLowerShriek f Λ) ≪≫
        Functor.leftUnitor (moduleUnboundedDerivedLowerShriek f Λ) =
      eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ (Category.id_comp f)) := by
  let af := moduleUnboundedDerivedLowerShriekAdjunction f Λ
  let ai := moduleUnboundedDerivedLowerShriekAdjunction (𝟙 S) Λ
  let atotal := moduleUnboundedDerivedLowerShriekAdjunction (𝟙 S ≫ f) Λ
  have hc : conjugateEquiv af atotal
      ((moduleUnboundedDerivedLowerShriekCompIso Λ f (𝟙 S)).hom ≫
        Functor.whiskerRight (moduleUnboundedDerivedLowerShriekIdIso Λ S).hom
          (moduleUnboundedDerivedLowerShriek f Λ) ≫
        (Functor.leftUnitor (moduleUnboundedDerivedLowerShriek f Λ)).hom) =
      (Functor.rightUnitor (moduleUnboundedDerivedInverseImage Λ f)).inv ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ f)
          (moduleUnboundedDerivedInverseImageIdIso Λ S).inv ≫
        (moduleUnboundedDerivedInverseImageCompIso Λ f (𝟙 S)).inv := by
    rw [← conjugateEquiv_comp _ (ai.comp af),
      ← conjugateEquiv_comp _ (Adjunction.id.comp af),
      conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
      conjugateEquiv_moduleUnboundedDerivedLowerShriekIdIso_hom,
        conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom]
    simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv af atotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, eqToIso.hom]
  rw [hc, conjugateEquiv_moduleUnboundedDerivedLowerShriek_eqToHom Λ (Category.id_comp f)]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    eqToIso.inv, Category.assoc] using congrArg Iso.inv
      (moduleUnboundedDerivedInverseImageCompIso_comp_id Λ f)

/-- The native lower-shriek comparison with the target identity is normalized. -/
theorem moduleUnboundedDerivedLowerShriekCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleUnboundedDerivedLowerShriekCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedLowerShriek f Λ)
          (moduleUnboundedDerivedLowerShriekIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleUnboundedDerivedLowerShriek f Λ) =
      eqToIso (moduleUnboundedDerivedLowerShriek_congr Λ (Category.comp_id f)) := by
  let af := moduleUnboundedDerivedLowerShriekAdjunction f Λ
  let ai := moduleUnboundedDerivedLowerShriekAdjunction (𝟙 X) Λ
  let atotal := moduleUnboundedDerivedLowerShriekAdjunction (f ≫ 𝟙 X) Λ
  have hc : conjugateEquiv af atotal
      ((moduleUnboundedDerivedLowerShriekCompIso Λ (𝟙 X) f).hom ≫
        Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek f Λ)
          (moduleUnboundedDerivedLowerShriekIdIso Λ X).hom ≫
        (Functor.rightUnitor (moduleUnboundedDerivedLowerShriek f Λ)).hom) =
      (Functor.leftUnitor (moduleUnboundedDerivedInverseImage Λ f)).inv ≫
        Functor.whiskerRight (moduleUnboundedDerivedInverseImageIdIso Λ X).inv
          (moduleUnboundedDerivedInverseImage Λ f) ≫
        (moduleUnboundedDerivedInverseImageCompIso Λ (𝟙 X) f).inv := by
    rw [← conjugateEquiv_comp _ (af.comp ai),
      ← conjugateEquiv_comp _ (af.comp Adjunction.id),
      conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
      conjugateEquiv_moduleUnboundedDerivedLowerShriekIdIso_hom,
        conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom]
    simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv af atotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, eqToIso.hom]
  rw [hc, conjugateEquiv_moduleUnboundedDerivedLowerShriek_eqToHom Λ (Category.comp_id f)]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    eqToIso.inv, Category.assoc] using congrArg Iso.inv
      (moduleUnboundedDerivedInverseImageCompIso_id_comp Λ f)


end AlgebraicGeometry.Scheme.EtaleCohomology
