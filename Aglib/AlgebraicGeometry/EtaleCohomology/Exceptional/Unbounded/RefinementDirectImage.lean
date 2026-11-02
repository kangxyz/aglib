/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Category
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralCoherence

/-!
# Direct-image comparison over the fixed compactification base

These are the original derived composition isomorphisms followed by equality
transport along the actual structural triangles. Coherence is inherited from
the original derived associativity and unit laws, with independent models.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wS wC wD wE

variable (Λ : Type (u + 1)) [Ring Λ]

section OverBase

variable {S C D E : Scheme.{u}}
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]

/-- Original direct-image composition along an actual triangle over a fixed base. -/
def moduleUnboundedDerivedDirectImageOverIso (pC : C ⟶ S) (pD : D ⟶ S)
    (a : C ⟶ D) (ha : a ≫ pD = pC) :
    moduleUnboundedDerivedDirectImage Λ a ⋙ moduleUnboundedDerivedDirectImage Λ pD ≅
      moduleUnboundedDerivedDirectImage Λ pC :=
  (moduleUnboundedDerivedDirectImageCompIso Λ pD a).symm ≪≫
    eqToIso (congrArg (fun k : C ⟶ S => moduleUnboundedDerivedDirectImage Λ k) ha)

variable [HasDerivedCategory.{wE} (ModuleSheaf E Λ)]

/-- Actual over-base triangles compose through the original derived associator. -/
theorem moduleUnboundedDerivedDirectImageOverIso_comp (pC : C ⟶ S) (pD : D ⟶ S)
    (pE : E ⟶ S) (a : C ⟶ D) (b : D ⟶ E)
    (ha : a ≫ pD = pC) (hb : b ≫ pE = pD)
    (hab : (a ≫ b) ≫ pE = pC) :
    Functor.isoWhiskerLeft (moduleUnboundedDerivedDirectImage Λ a)
        (moduleUnboundedDerivedDirectImageOverIso Λ pD pE b hb) ≪≫
      moduleUnboundedDerivedDirectImageOverIso Λ pC pD a ha =
    (Functor.associator (moduleUnboundedDerivedDirectImage Λ a)
        (moduleUnboundedDerivedDirectImage Λ b)
        (moduleUnboundedDerivedDirectImage Λ pE)).symm ≪≫
      Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageCompIso Λ b a).symm
        (moduleUnboundedDerivedDirectImage Λ pE) ≪≫
      moduleUnboundedDerivedDirectImageOverIso Λ pC pE (a ≫ b) hab := by
  subst pC
  subst pD
  apply Iso.ext
  simpa only [moduleUnboundedDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl,
    Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, eqToIso.inv, eqToIso.hom] using
    congrArg Iso.hom (inverseStructural_assoc
      (moduleUnboundedDerivedDirectImageCompIso Λ b a)
      (moduleUnboundedDerivedDirectImageCompIso Λ pE b)
      (moduleUnboundedDerivedDirectImageCompIso Λ (b ≫ pE) a)
      (moduleUnboundedDerivedDirectImageCompIso Λ pE (a ≫ b))
      (eqToIso (congrArg (fun k : C ⟶ S => moduleUnboundedDerivedDirectImage Λ k)
        (Category.assoc a b pE).symm))
      (moduleUnboundedDerivedDirectImageCompIso_assoc Λ pE b a))

end OverBase

section Refinement

variable {X S : Scheme.{u}} {f : X ⟶ S}
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- Direct images along an actual compactification refinement retain the original
composition comparison and the original structural triangle. -/
def moduleUnboundedDerivedRefinementDirectImageIso {C D : Hom.DenseCompactification f}
    (a : C ⟶ D)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)] :
    moduleUnboundedDerivedDirectImage Λ a.hom ⋙ moduleUnboundedDerivedDirectImage Λ D.p ≅
      moduleUnboundedDerivedDirectImage Λ C.p :=
  moduleUnboundedDerivedDirectImageOverIso Λ C.p D.p a.hom a.base_fac

/-- Identity refinements give the original derived identity normalization. -/
theorem moduleUnboundedDerivedRefinementDirectImageIso_id (C : Hom.DenseCompactification f)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)] :
    moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C) =
      Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageIdIso Λ C.Xbar)
          (moduleUnboundedDerivedDirectImage Λ C.p) ≪≫
        Functor.leftUnitor (moduleUnboundedDerivedDirectImage Λ C.p) := by
  have h := structuralIso_normalization
    (moduleUnboundedDerivedDirectImageCompIso Λ C.p (𝟙 C.Xbar))
    (Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageIdIso Λ C.Xbar)
      (moduleUnboundedDerivedDirectImage Λ C.p) ≪≫
        Functor.leftUnitor (moduleUnboundedDerivedDirectImage Λ C.p))
    (eqToIso (congrArg (fun k : C.Xbar ⟶ S => moduleUnboundedDerivedDirectImage Λ k)
      (Category.id_comp C.p)))
    (moduleUnboundedDerivedDirectImageCompIso_comp_id Λ C.p)
  simpa only [moduleUnboundedDerivedRefinementDirectImageIso,
    moduleUnboundedDerivedDirectImageOverIso, Hom.DenseCompactification.id_hom] using h

/-- Refinement direct-image comparisons compose with the original derived compositor. -/
theorem moduleUnboundedDerivedRefinementDirectImageIso_comp
    {C D E : Hom.DenseCompactification f} (a : C ⟶ D) (b : D ⟶ E)
    [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]
    [HasDerivedCategory.{wE} (ModuleSheaf E.Xbar Λ)] :
    Functor.isoWhiskerLeft (moduleUnboundedDerivedDirectImage Λ a.hom)
        (moduleUnboundedDerivedRefinementDirectImageIso Λ b) ≪≫
      moduleUnboundedDerivedRefinementDirectImageIso Λ a =
    (Functor.associator (moduleUnboundedDerivedDirectImage Λ a.hom)
        (moduleUnboundedDerivedDirectImage Λ b.hom)
        (moduleUnboundedDerivedDirectImage Λ E.p)).symm ≪≫
      Functor.isoWhiskerRight (moduleUnboundedDerivedDirectImageCompIso Λ b.hom a.hom).symm
        (moduleUnboundedDerivedDirectImage Λ E.p) ≪≫
      moduleUnboundedDerivedRefinementDirectImageIso Λ (a ≫ b) :=
  moduleUnboundedDerivedDirectImageOverIso_comp Λ C.p D.p E.p a.hom b.hom
    a.base_fac b.base_fac (a ≫ b).base_fac

end Refinement

end AlgebraicGeometry.Scheme.EtaleCohomology
