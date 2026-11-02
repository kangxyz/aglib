/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CompositionCoherence
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.CompositionPredicate

/-! # Coherence of the original lower-shriek compositors -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wT wV
variable (Λ : Type (u + 1)) [Ring Λ]

/-- Equality transport has the reversed original inverse-image mate. -/
theorem conjugateEquiv_moduleLowerShriek_eqToHom {X S : Scheme.{u}}
    {f g : S ⟶ X} [Etale f] [Etale g] (h : f = g) :
    conjugateEquiv (moduleLowerShriekAdjunction g Λ) (moduleLowerShriekAdjunction f Λ)
      (eqToHom (moduleLowerShriek_congr Λ h)) =
      eqToHom (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) h.symm) := by
  subst g
  simp

/-- The exact original lower-shriek compositors associate. -/
theorem moduleLowerShriekCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) [Etale f] [Etale g] [Etale h] :
    moduleLowerShriekCompIso Λ (g ≫ f) h ≪≫
        Functor.isoWhiskerLeft (moduleLowerShriek h Λ) (moduleLowerShriekCompIso Λ f g) =
      eqToIso (moduleLowerShriek_congr Λ (Category.assoc h g f).symm) ≪≫
        moduleLowerShriekCompIso Λ f (h ≫ g) ≪≫
        Functor.isoWhiskerRight (moduleLowerShriekCompIso Λ g h) (moduleLowerShriek f Λ) ≪≫
        Functor.associator (moduleLowerShriek h Λ)
          (moduleLowerShriek g Λ) (moduleLowerShriek f Λ) := by
  let af := moduleLowerShriekAdjunction f Λ
  let ag := moduleLowerShriekAdjunction g Λ
  let ah := moduleLowerShriekAdjunction h Λ
  let afg := moduleLowerShriekAdjunction (g ≫ f) Λ
  let agh := moduleLowerShriekAdjunction (h ≫ g) Λ
  let adjTotal :=  moduleLowerShriekAdjunction (h ≫ (g ≫ f)) Λ
  let adjTotalAssoc :=  moduleLowerShriekAdjunction ((h ≫ g) ≫ f) Λ
  have hL : conjugateEquiv (ah.comp (ag.comp af)) adjTotal
      ((moduleLowerShriekCompIso Λ (g ≫ f) h).hom ≫
        Functor.whiskerLeft (moduleLowerShriek h Λ) (moduleLowerShriekCompIso Λ f g).hom) =
      Functor.whiskerRight (moduleInverseImageCompIso Λ f g).inv (moduleInverseImage h Λ) ≫
        (moduleInverseImageCompIso Λ (g ≫ f) h).inv := by
    rw [← conjugateEquiv_comp _ (ah.comp afg), conjugateEquiv_whiskerLeft,
      conjugateEquiv_moduleLowerShriekCompIso_hom,
      conjugateEquiv_moduleLowerShriekCompIso_hom]
  have hR : conjugateEquiv (ah.comp (ag.comp af)) adjTotal
      (eqToHom (moduleLowerShriek_congr Λ (Category.assoc h g f).symm) ≫
        (moduleLowerShriekCompIso Λ f (h ≫ g)).hom ≫
        Functor.whiskerRight (moduleLowerShriekCompIso Λ g h).hom (moduleLowerShriek f Λ) ≫
        (Functor.associator (moduleLowerShriek h Λ)
          (moduleLowerShriek g Λ) (moduleLowerShriek f Λ)).hom) =
      (Functor.associator (moduleInverseImage f Λ)
        (moduleInverseImage g Λ) (moduleInverseImage h Λ)).hom ≫
        Functor.whiskerLeft (moduleInverseImage f Λ) (moduleInverseImageCompIso Λ g h).inv ≫
        (moduleInverseImageCompIso Λ f (h ≫ g)).inv ≫
        eqToHom (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ)
          (Category.assoc h g f)) := by
    rw [← conjugateEquiv_comp _ adjTotalAssoc, ← conjugateEquiv_comp _ (agh.comp af),
      ← conjugateEquiv_comp _ ((ah.comp ag).comp af),
      conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
      conjugateEquiv_moduleLowerShriekCompIso_hom,
      conjugateEquiv_moduleLowerShriekCompIso_hom,
      conjugateEquiv_moduleLowerShriek_eqToHom]
    all_goals simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv (ah.comp (ag.comp af)) adjTotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    eqToIso.hom]
  rw [hL, hR]
  apply NatTrans.ext
  funext M
  have hi := congrArg (fun e => e.inv.app M) (moduleInverseImageCompIso_assoc Λ f g h)
  have hi' := congrArg (fun t => t ≫ eqToHom
    (congrArg (fun k : V ⟶ X => (moduleInverseImage k Λ).obj M)
      (Category.assoc h g f))) hi.symm
  simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    eqToIso.inv, eqToHom_app, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using hi'

/-- The native lower-shriek comparison with the source identity is normalized. -/
theorem moduleLowerShriekCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] :
    moduleLowerShriekCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerRight (moduleLowerShriekIdIso Λ S) (moduleLowerShriek f Λ) ≪≫
        Functor.leftUnitor (moduleLowerShriek f Λ) =
      eqToIso (moduleLowerShriek_congr Λ (Category.id_comp f)) := by
  let af := moduleLowerShriekAdjunction f Λ
  let ai := moduleLowerShriekAdjunction (𝟙 S) Λ
  let atotal := moduleLowerShriekAdjunction (𝟙 S ≫ f) Λ
  have hc : conjugateEquiv af atotal
      ((moduleLowerShriekCompIso Λ f (𝟙 S)).hom ≫
        Functor.whiskerRight (moduleLowerShriekIdIso Λ S).hom (moduleLowerShriek f Λ) ≫
        (Functor.leftUnitor (moduleLowerShriek f Λ)).hom) =
      (Functor.rightUnitor (moduleInverseImage f Λ)).inv ≫
        Functor.whiskerLeft (moduleInverseImage f Λ) (moduleInverseImageIdIso Λ S).inv ≫
        (moduleInverseImageCompIso Λ f (𝟙 S)).inv := by
    rw [← conjugateEquiv_comp _ (ai.comp af),
      ← conjugateEquiv_comp _ (Adjunction.id.comp af),
      conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
      conjugateEquiv_moduleLowerShriekIdIso_hom, conjugateEquiv_moduleLowerShriekCompIso_hom]
    simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv af atotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, eqToIso.hom]
  rw [hc, conjugateEquiv_moduleLowerShriek_eqToHom Λ (Category.id_comp f)]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    eqToIso.inv, Category.assoc] using congrArg Iso.inv (moduleInverseImageCompIso_comp_id Λ f)

/-- The native lower-shriek comparison with the target identity is normalized. -/
theorem moduleLowerShriekCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] :
    moduleLowerShriekCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (moduleLowerShriek f Λ) (moduleLowerShriekIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleLowerShriek f Λ) =
      eqToIso (moduleLowerShriek_congr Λ (Category.comp_id f)) := by
  let af := moduleLowerShriekAdjunction f Λ
  let ai := moduleLowerShriekAdjunction (𝟙 X) Λ
  let atotal := moduleLowerShriekAdjunction (f ≫ 𝟙 X) Λ
  have hc : conjugateEquiv af atotal
      ((moduleLowerShriekCompIso Λ (𝟙 X) f).hom ≫
        Functor.whiskerLeft (moduleLowerShriek f Λ) (moduleLowerShriekIdIso Λ X).hom ≫
        (Functor.rightUnitor (moduleLowerShriek f Λ)).hom) =
      (Functor.leftUnitor (moduleInverseImage f Λ)).inv ≫
        Functor.whiskerRight (moduleInverseImageIdIso Λ X).inv (moduleInverseImage f Λ) ≫
        (moduleInverseImageCompIso Λ (𝟙 X) f).inv := by
    rw [← conjugateEquiv_comp _ (af.comp ai),
      ← conjugateEquiv_comp _ (af.comp Adjunction.id),
      conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
      conjugateEquiv_moduleLowerShriekIdIso_hom, conjugateEquiv_moduleLowerShriekCompIso_hom]
    simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv af atotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, eqToIso.hom]
  rw [hc, conjugateEquiv_moduleLowerShriek_eqToHom Λ (Category.comp_id f)]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    eqToIso.inv, Category.assoc] using congrArg Iso.inv (moduleInverseImageCompIso_id_comp Λ f)


/-- The original derived lower-shriek comparison is normalized at the source identity. -/
theorem moduleDerivedLowerShriekCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleDerivedLowerShriekCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerRight (moduleDerivedLowerShriekIdIso Λ S)
          (moduleDerivedLowerShriek f Λ) ≪≫
        Functor.leftUnitor (moduleDerivedLowerShriek f Λ) =
      eqToIso (moduleDerivedLowerShriek_congr Λ (Category.id_comp f)) := by
  let F := moduleLowerShriek f Λ
  let I := moduleLowerShriek (𝟙 S) Λ
  let P := moduleLowerShriek (𝟙 S ≫ f) Λ
  let e := moduleLowerShriekIdIso Λ S
  let c := moduleLowerShriekCompIso Λ f (𝟙 S)
  have hn := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_left F e
  have hu := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_leftUnitor F
  have hp := congrArg (fun z : P ≅ F => P.rightDerivedFunctorPlusIso z)
    (moduleLowerShriekCompIso_comp_id Λ f)
  simp only [Functor.rightDerivedFunctorPlusIso_trans,
    Functor.rightDerivedFunctorPlusIso_eqToIso] at hp
  change (P.rightDerivedFunctorPlusIso c ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology I F) ≪≫
      Functor.isoWhiskerRight (I.rightDerivedFunctorPlusIso e ≪≫
        Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf S Λ)) F.rightDerivedFunctorPlus ≪≫
      Functor.leftUnitor F.rightDerivedFunctorPlus = _
  simp only [Functor.isoWhiskerRight_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology I F),
    ← hn]
  simp only [Iso.trans_assoc]
  rw [hu]
  exact hp

/-- The original derived lower-shriek comparison is normalized at the target identity. -/
theorem moduleDerivedLowerShriekCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleDerivedLowerShriekCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (moduleDerivedLowerShriek f Λ)
          (moduleDerivedLowerShriekIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleDerivedLowerShriek f Λ) =
      eqToIso (moduleDerivedLowerShriek_congr Λ (Category.comp_id f)) := by
  let F := moduleLowerShriek f Λ
  let I := moduleLowerShriek (𝟙 X) Λ
  let P := moduleLowerShriek (f ≫ 𝟙 X) Λ
  let e := moduleLowerShriekIdIso Λ X
  let c := moduleLowerShriekCompIso Λ (𝟙 X) f
  have hn := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_right F e
  have hu := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_rightUnitor F
  have hp := congrArg (fun z : P ≅ F => P.rightDerivedFunctorPlusIso z)
    (moduleLowerShriekCompIso_id_comp Λ f)
  simp only [Functor.rightDerivedFunctorPlusIso_trans,
    Functor.rightDerivedFunctorPlusIso_eqToIso] at hp
  change (P.rightDerivedFunctorPlusIso c ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology F I) ≪≫
      Functor.isoWhiskerLeft F.rightDerivedFunctorPlus (I.rightDerivedFunctorPlusIso e ≪≫
        Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf X Λ)) ≪≫
      Functor.rightUnitor F.rightDerivedFunctorPlus = _
  simp only [Functor.isoWhiskerLeft_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology F I),
    ← hn]
  simp only [Iso.trans_assoc]
  rw [hu]
  exact hp

/-- The original derived lower-shriek compositors associate. The regular typed
predicate preserves the whole original equation without unfolding native sites. -/
theorem moduleDerivedLowerShriekCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) [Etale f] [Etale g] [Etale h]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)] :
    Functor.CompositionAssociates
      (eqToIso (moduleDerivedLowerShriek_congr Λ (Category.assoc h g f).symm))
      (moduleDerivedLowerShriekCompIso Λ (g ≫ f) h)
      (moduleDerivedLowerShriekCompIso Λ f g)
      (moduleDerivedLowerShriekCompIso Λ f (h ≫ g))
      (moduleDerivedLowerShriekCompIso Λ g h) := by
  exact Functor.rightDerivedFunctorPlus_compositionAssociates
    (moduleLowerShriek h Λ) (moduleLowerShriek g Λ) (moduleLowerShriek f Λ)
    (moduleLowerShriek (h ≫ g) Λ) (moduleLowerShriek (g ≫ f) Λ)
    (moduleLowerShriek (h ≫ (g ≫ f)) Λ) (moduleLowerShriek ((h ≫ g) ≫ f) Λ)
    (eqToIso (moduleLowerShriek_congr Λ (Category.assoc h g f).symm))
    (moduleLowerShriekCompIso Λ (g ≫ f) h) (moduleLowerShriekCompIso Λ f g)
    (moduleLowerShriekCompIso Λ f (h ≫ g)) (moduleLowerShriekCompIso Λ g h)
    (moduleLowerShriekCompIso_assoc Λ f g h)
    (eqToIso (moduleDerivedLowerShriek_congr Λ (Category.assoc h g f).symm))
    (Functor.rightDerivedFunctorPlusIso_eqToIso _ _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
