/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Category
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Transport
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityBranches

/-!
# Coherence of the original derived module direct-image comparisons

Associativity and identities retain the original module comparisons through the
installed generic right-derived coherence laws. Actual over-base triangles and
compactification refinements specialize those same maps. All endpoint and middle
derived-category realizations remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wT wV wC wD wE

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Whole-isomorphism form of the original direct-image associativity equation. -/
theorem moduleDirectImageCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    moduleDirectImageCompIso Λ (g ≫ f) h ≪≫
        Functor.isoWhiskerLeft (moduleDirectImage h Λ) (moduleDirectImageCompIso Λ f g) =
      (eqToIso (congrArg (fun k : V ⟶ X => moduleDirectImage k Λ)
          (Category.assoc h g f).symm) ≪≫ moduleDirectImageCompIso Λ f (h ≫ g)) ≪≫
        Functor.isoWhiskerRight (moduleDirectImageCompIso Λ g h) (moduleDirectImage f Λ) ≪≫
        Functor.associator (moduleDirectImage h Λ)
          (moduleDirectImage g Λ) (moduleDirectImage f Λ) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext M
  simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, eqToIso.inv, eqToIso.hom, eqToHom_app,
    Category.assoc] using (moduleDirectImageCompIso_assoc_app Λ f g h M).symm

/-- Original derived direct images associate, including the base-map equality transport. -/
theorem moduleDerivedDirectImageCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)] :
    moduleDerivedDirectImageCompIso Λ (g ≫ f) h ≪≫
        Functor.isoWhiskerLeft (moduleDerivedDirectImage Λ h)
          (moduleDerivedDirectImageCompIso Λ f g) =
      eqToIso (congrArg (fun k : V ⟶ X => moduleDerivedDirectImage Λ k)
          (Category.assoc h g f).symm) ≪≫
        moduleDerivedDirectImageCompIso Λ f (h ≫ g) ≪≫
        Functor.isoWhiskerRight (moduleDerivedDirectImageCompIso Λ g h)
          (moduleDerivedDirectImage Λ f) ≪≫
        Functor.associator (moduleDerivedDirectImage Λ h)
          (moduleDerivedDirectImage Λ g) (moduleDerivedDirectImage Λ f) := by
  simpa only [moduleDerivedDirectImageCompIso, Functor.rightDerivedFunctorPlusIso_trans,
    Functor.rightDerivedFunctorPlusIso_eqToIso, Iso.trans_assoc] using
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_transportAssoc
      (moduleDirectImage h Λ) (moduleDirectImage g Λ) (moduleDirectImage f Λ)
      (moduleDirectImage (h ≫ g) Λ) (moduleDirectImage (g ≫ f) Λ)
      (moduleDirectImage (h ≫ (g ≫ f)) Λ)
      (moduleDirectImageCompIso Λ (g ≫ f) h) (moduleDirectImageCompIso Λ f g)
      (eqToIso (congrArg (fun k : V ⟶ X => moduleDirectImage k Λ)
        (Category.assoc h g f).symm) ≪≫ moduleDirectImageCompIso Λ f (h ≫ g))
      (moduleDirectImageCompIso Λ g h) (moduleDirectImageCompIso_assoc Λ f g h)

/-- The original derived direct-image comparison is normalized at the source identity. -/
theorem moduleDerivedDirectImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleDerivedDirectImageCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerRight (moduleDerivedDirectImageIdIso Λ S)
          (moduleDerivedDirectImage Λ f) ≪≫
        Functor.leftUnitor (moduleDerivedDirectImage Λ f) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleDerivedDirectImage Λ k)
        (Category.id_comp f)) := by
  let F := moduleDirectImage f Λ
  let I := moduleDirectImage (𝟙 S) Λ
  let P := moduleDirectImage (𝟙 S ≫ f) Λ
  let e := moduleDirectImageIdIso Λ S
  let c := moduleDirectImageCompIso Λ f (𝟙 S)
  have hn := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_left F e
  have hu := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_leftUnitor F
  have hp := congrArg (fun z : P ≅ F => P.rightDerivedFunctorPlusIso z)
    (moduleDirectImageCompIso_comp_id Λ f)
  simp only [Functor.rightDerivedFunctorPlusIso_trans,
    Functor.rightDerivedFunctorPlusIso_eqToIso] at hp
  change (P.rightDerivedFunctorPlusIso c ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives I F) ≪≫
      Functor.isoWhiskerRight (I.rightDerivedFunctorPlusIso e ≪≫
        Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf S Λ)) F.rightDerivedFunctorPlus ≪≫
      Functor.leftUnitor F.rightDerivedFunctorPlus = _
  simp only [Functor.isoWhiskerRight_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives I F),
    ← hn]
  simp only [Iso.trans_assoc]
  rw [hu]
  exact hp

/-- The original derived direct-image comparison is normalized at the target identity. -/
theorem moduleDerivedDirectImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleDerivedDirectImageCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (moduleDerivedDirectImage Λ f)
          (moduleDerivedDirectImageIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleDerivedDirectImage Λ f) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleDerivedDirectImage Λ k)
        (Category.comp_id f)) := by
  let F := moduleDirectImage f Λ
  let I := moduleDirectImage (𝟙 X) Λ
  let P := moduleDirectImage (f ≫ 𝟙 X) Λ
  let e := moduleDirectImageIdIso Λ X
  let c := moduleDirectImageCompIso Λ (𝟙 X) f
  have hn := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_right F e
  have hu := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_rightUnitor F
  have hp := congrArg (fun z : P ≅ F => P.rightDerivedFunctorPlusIso z)
    (moduleDirectImageCompIso_id_comp Λ f)
  simp only [Functor.rightDerivedFunctorPlusIso_trans,
    Functor.rightDerivedFunctorPlusIso_eqToIso] at hp
  change (P.rightDerivedFunctorPlusIso c ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives F I) ≪≫
      Functor.isoWhiskerLeft F.rightDerivedFunctorPlus (I.rightDerivedFunctorPlusIso e ≪≫
        Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf X Λ)) ≪≫
      Functor.rightUnitor F.rightDerivedFunctorPlus = _
  simp only [Functor.isoWhiskerLeft_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives F I),
    ← hn]
  simp only [Iso.trans_assoc]
  rw [hu]
  exact hp

section OverBase

variable {S C D E : Scheme.{u}}
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]

/-- Original direct-image composition along an actual triangle over a fixed base. -/
def moduleDerivedDirectImageOverIso (pC : C ⟶ S) (pD : D ⟶ S)
    (a : C ⟶ D) (ha : a ≫ pD = pC) :
    moduleDerivedDirectImage Λ a ⋙ moduleDerivedDirectImage Λ pD ≅
      moduleDerivedDirectImage Λ pC :=
  (moduleDerivedDirectImageCompIso Λ pD a).symm ≪≫
    eqToIso (congrArg (fun k : C ⟶ S => moduleDerivedDirectImage Λ k) ha)

variable [HasDerivedCategory.{wE} (ModuleSheaf E Λ)]

/-- Actual over-base triangles compose through the original derived associator. -/
theorem moduleDerivedDirectImageOverIso_comp (pC : C ⟶ S) (pD : D ⟶ S)
    (pE : E ⟶ S) (a : C ⟶ D) (b : D ⟶ E)
    (ha : a ≫ pD = pC) (hb : b ≫ pE = pD)
    (hab : (a ≫ b) ≫ pE = pC) :
    Functor.isoWhiskerLeft (moduleDerivedDirectImage Λ a)
        (moduleDerivedDirectImageOverIso Λ pD pE b hb) ≪≫
      moduleDerivedDirectImageOverIso Λ pC pD a ha =
    (Functor.associator (moduleDerivedDirectImage Λ a)
        (moduleDerivedDirectImage Λ b) (moduleDerivedDirectImage Λ pE)).symm ≪≫
      Functor.isoWhiskerRight (moduleDerivedDirectImageCompIso Λ b a).symm
        (moduleDerivedDirectImage Λ pE) ≪≫
      moduleDerivedDirectImageOverIso Λ pC pE (a ≫ b) hab := by
  subst pC
  subst pD
  apply Iso.ext
  simpa only [moduleDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl,
    Iso.trans_symm, Functor.isoWhiskerLeft_symm, Functor.isoWhiskerRight_symm,
    Iso.symm_symm_eq, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom,
    eqToIso.inv, eqToIso.hom] using
    congrArg Iso.hom (congrArg Iso.symm
      (moduleDerivedDirectImageCompIso_assoc Λ pE b a))

end OverBase

section Refinement

variable {X S : Scheme.{u}} {f : X ⟶ S}
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- Direct images along an actual compactification refinement retain the original
composition comparison and the original structural triangle. -/
def moduleDerivedRefinementDirectImageIso {C D : Hom.DenseCompactification f}
    (a : C ⟶ D)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)] :
    moduleDerivedDirectImage Λ a.hom ⋙ moduleDerivedDirectImage Λ D.p ≅
      moduleDerivedDirectImage Λ C.p :=
  moduleDerivedDirectImageOverIso Λ C.p D.p a.hom a.base_fac

/-- Identity refinements give the original derived identity normalization. -/
theorem moduleDerivedRefinementDirectImageIso_id (C : Hom.DenseCompactification f)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)] :
    moduleDerivedRefinementDirectImageIso Λ (𝟙 C) =
      Functor.isoWhiskerRight (moduleDerivedDirectImageIdIso Λ C.Xbar)
          (moduleDerivedDirectImage Λ C.p) ≪≫
        Functor.leftUnitor (moduleDerivedDirectImage Λ C.p) := by
  have h := congrArg
    (fun e => (moduleDerivedDirectImageCompIso Λ C.p (𝟙 C.Xbar)).symm ≪≫ e)
    (moduleDerivedDirectImageCompIso_comp_id Λ C.p)
  simpa only [moduleDerivedRefinementDirectImageIso, moduleDerivedDirectImageOverIso,
    Hom.DenseCompactification.id_hom, Iso.trans_assoc, Iso.symm_self_id_assoc] using h.symm

/-- Refinement direct-image comparisons compose with the original derived compositor. -/
theorem moduleDerivedRefinementDirectImageIso_comp
    {C D E : Hom.DenseCompactification f} (a : C ⟶ D) (b : D ⟶ E)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]
    [HasDerivedCategory.{wE} (ModuleSheaf E.Xbar Λ)] :
    Functor.isoWhiskerLeft (moduleDerivedDirectImage Λ a.hom)
        (moduleDerivedRefinementDirectImageIso Λ b) ≪≫
      moduleDerivedRefinementDirectImageIso Λ a =
    (Functor.associator (moduleDerivedDirectImage Λ a.hom)
        (moduleDerivedDirectImage Λ b.hom) (moduleDerivedDirectImage Λ E.p)).symm ≪≫
      Functor.isoWhiskerRight (moduleDerivedDirectImageCompIso Λ b.hom a.hom).symm
        (moduleDerivedDirectImage Λ E.p) ≪≫
      moduleDerivedRefinementDirectImageIso Λ (a ≫ b) :=
  moduleDerivedDirectImageOverIso_comp Λ C.p D.p E.p a.hom b.hom
    a.base_fac b.base_fac (a ≫ b).base_fac

end Refinement

end AlgebraicGeometry.Scheme.EtaleCohomology
