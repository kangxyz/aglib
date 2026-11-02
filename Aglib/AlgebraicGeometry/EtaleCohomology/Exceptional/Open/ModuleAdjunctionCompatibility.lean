/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange
public import Aglib.CategoryTheory.Adjunction.UnderlyingEquivalence
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ValuedComparison

/-! # Original native-to-valued adjunction compatibility -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

/-- The direct-image transport cancels by the original inverse-equivalence unit. -/
@[reassoc]
theorem moduleDirectImageTransportIso_inv_comparison (M : ModuleSheaf S Λ) :
    (moduleSheafEquivalence X Λ).inverse.map
        ((moduleDirectImageTransportIso f Λ).inv.app M) ≫
      (moduleDirectImageComparison f Λ).hom.app M =
    (moduleSheafEquivalence X Λ).unitIso.inv.app
      ((moduleValuedDirectImage f Λ).obj ((moduleSheafEquivalence S Λ).inverse.obj M)) := by
  exact ValuedComparison.rightInverse_comparison (moduleSheafEquivalence X Λ)
    (moduleDirectImage f Λ) (moduleSheafEquivalence S Λ).inverse
    (moduleValuedDirectImage f Λ) (moduleDirectImageComparison f Λ)
    (moduleDirectImageTransportIso f Λ) (fun M => Equivalence.transportRightIso_inv_app
      (moduleSheafEquivalence X Λ) (moduleDirectImage f Λ)
      (moduleSheafEquivalence S Λ).inverse (moduleValuedDirectImage f Λ)
      (moduleDirectImageComparison f Λ) M) M

/-- The transported adjunction unit recovers the actual valued unit and the source unit. -/
@[reassoc]
theorem moduleTransportAdjunction_unit_comparison (M : ModuleSheaf X Λ) :
    (moduleSheafEquivalence X Λ).inverse.map ((moduleTransportAdjunction f Λ).unit.app M) ≫
      (moduleDirectImageComparison f Λ).hom.app
        ((((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ) ⋙
          (moduleSheafEquivalence S Λ).functor).obj M) =
    (moduleValuedInverseImageAdjunction f Λ).unit.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) ≫
      (moduleValuedDirectImage f Λ).map ((moduleSheafEquivalence S Λ).unitIso.hom.app
        ((moduleValuedInverseImage f Λ).obj ((moduleSheafEquivalence X Λ).inverse.obj M))) := by
  exact ValuedComparison.transportUnit_comparison
    (moduleSheafEquivalence X Λ) (moduleSheafEquivalence S Λ)
    (moduleValuedInverseImageAdjunction f Λ) (moduleDirectImage f Λ)
    (moduleDirectImageComparison f Λ) (moduleDirectImageTransportIso f Λ)
    (fun M => Equivalence.transportRightIso_inv_app
      (moduleSheafEquivalence X Λ) (moduleDirectImage f Λ)
      (moduleSheafEquivalence S Λ).inverse (moduleValuedDirectImage f Λ)
      (moduleDirectImageComparison f Λ) M) M

/-- The actual native and valued pullback units form the original adjunction square. -/
@[reassoc]
theorem moduleInverseImageValuedIso_unit (M : ModuleSheaf X Λ) :
    (moduleSheafEquivalence X Λ).inverse.map
        ((moduleInverseImageAdjunction f Λ).unit.app M) ≫
      (moduleDirectImageComparison f Λ).hom.app ((moduleInverseImage f Λ).obj M) ≫
      (moduleValuedDirectImage f Λ).map ((moduleInverseImageValuedIso Λ f).hom.app M) =
    (moduleValuedInverseImageAdjunction f Λ).unit.app
      ((moduleSheafEquivalence X Λ).inverse.obj M) := by
  exact ValuedComparison.inverseValuedIso_unit
    (moduleSheafEquivalence X Λ) (moduleSheafEquivalence S Λ)
    (moduleValuedInverseImageAdjunction f Λ) (moduleInverseImageAdjunction f Λ)
    (moduleDirectImageComparison f Λ) (moduleDirectImageTransportIso f Λ)
    (moduleInverseImageTransportIso f Λ) (fun M => Equivalence.transportRightIso_inv_app
      (moduleSheafEquivalence X Λ) (moduleDirectImage f Λ)
      (moduleSheafEquivalence S Λ).inverse (moduleValuedDirectImage f Λ)
      (moduleDirectImageComparison f Λ) M)
    (moduleInverseImageTransportIso_unit f Λ) M

end AlgebraicGeometry.Scheme.EtaleCohomology
