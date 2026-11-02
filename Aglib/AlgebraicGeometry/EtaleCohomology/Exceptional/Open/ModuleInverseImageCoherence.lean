/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleDirectImageCoherence
public import Aglib.CategoryTheory.Adjunction.Mates.SelectedCoherence

/-! # Native inverse-image composition and its original adjunction mate -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Native inverse-image composition is exactly the mate of native direct-image composition. -/
theorem conjugateEquiv_moduleInverseImageCompIso_hom {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    conjugateEquiv ((moduleInverseImageAdjunction f Λ).comp
        (moduleInverseImageAdjunction g Λ)) (moduleInverseImageAdjunction (g ≫ f) Λ)
      (moduleInverseImageCompIso Λ f g).hom = (moduleDirectImageCompIso Λ f g).inv := by
  rw [moduleInverseImageCompIso_eq_original]
  exact conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (moduleInverseImageAdjunction (g ≫ f) Λ)
    ((moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g Λ))
    (moduleDirectImageCompIso Λ f g)

/-- Equality transport for native inverse images has the reversed original direct-image mate. -/
theorem conjugateEquiv_moduleInverseImage_eqToHom {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) :
    conjugateEquiv (moduleInverseImageAdjunction g Λ) (moduleInverseImageAdjunction f Λ)
        (eqToHom (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) h)) =
      eqToHom (congrArg (fun k : S ⟶ X => moduleDirectImage k Λ) h.symm) := by
  subst g
  simp

/-- Native inverse-image composition associates with its original base-map transport. -/
theorem moduleInverseImageCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    moduleInverseImageCompIso Λ f (h ≫ g) ≪≫
        Functor.isoWhiskerLeft (moduleInverseImage f Λ) (moduleInverseImageCompIso Λ g h) =
      eqToIso (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ) (Category.assoc h g f)) ≪≫
        moduleInverseImageCompIso Λ (g ≫ f) h ≪≫
        Functor.isoWhiskerRight (moduleInverseImageCompIso Λ f g) (moduleInverseImage h Λ) ≪≫
        Functor.associator (moduleInverseImage f Λ)
          (moduleInverseImage g Λ) (moduleInverseImage h Λ) := by
  exact CategoryTheory.SelectedAdjointCoherence.assoc_of_right_app
    (fun k : V ⟶ X => moduleInverseImage k Λ)
    (fun k : V ⟶ X => moduleDirectImage k Λ) (fun k => moduleInverseImageAdjunction k Λ)
    (moduleInverseImageAdjunction f Λ) (moduleInverseImageAdjunction g Λ)
    (moduleInverseImageAdjunction h Λ) (moduleInverseImageAdjunction (g ≫ f) Λ)
    (moduleInverseImageAdjunction (h ≫ g) Λ) (Category.assoc h g f)
    (moduleInverseImageCompIso Λ f g) (moduleInverseImageCompIso Λ g h)
    (moduleInverseImageCompIso Λ f (h ≫ g)) (moduleInverseImageCompIso Λ (g ≫ f) h)
    (moduleDirectImageCompIso Λ f g).symm (moduleDirectImageCompIso Λ g h).symm
    (moduleDirectImageCompIso Λ f (h ≫ g)).symm
    (moduleDirectImageCompIso Λ (g ≫ f) h).symm
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ f g)
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ g h)
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ f (h ≫ g))
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ (g ≫ f) h)
    (fun M => by
      simpa only [Iso.symm_hom, eqToIso.hom, eqToHom_app] using
        moduleDirectImageCompIso_assoc_app Λ f g h M)

end AlgebraicGeometry.Scheme.EtaleCohomology
