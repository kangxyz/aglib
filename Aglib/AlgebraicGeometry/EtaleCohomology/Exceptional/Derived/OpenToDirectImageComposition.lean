/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition
public import Aglib.CategoryTheory.Adjunction.TripleCompositionTransport

/-! # The same native canonical open comparison respects original composition -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wV wX
variable (Λ : Type (u + 1)) [Ring Λ] {U V X : Scheme.{u}}
  (j : U ⟶ V) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- Both actual compositors preserve the original canonical outer-adjoint maps. -/
theorem moduleDerivedLowerShriekToDirectImage_comp :
    Adjunction.TripleCompositionTransportEquation
      (moduleDerivedOpenTriple Λ (j ≫ k)) (moduleDerivedOpenTriple Λ j)
      (moduleDerivedOpenTriple Λ k) (moduleDerivedLowerShriekCompIso Λ k j)
      (moduleDerivedDirectImageCompIso Λ k j) :=
  Adjunction.Triple.leftToRight_comp_transport
    (moduleDerivedOpenTriple Λ (j ≫ k)) (moduleDerivedOpenTriple Λ j)
    (moduleDerivedOpenTriple Λ k) (moduleDerivedLowerShriekCompIso Λ k j)
    (moduleDerivedInverseImageCompIso Λ k j) (moduleDerivedDirectImageCompIso Λ k j)
    (conjugateEquiv_moduleDerivedLowerShriekCompIso_hom Λ k j)
    (conjugateEquiv_moduleDerivedInverseImageCompIso_hom Λ k j)

end AlgebraicGeometry.Scheme.EtaleCohomology
