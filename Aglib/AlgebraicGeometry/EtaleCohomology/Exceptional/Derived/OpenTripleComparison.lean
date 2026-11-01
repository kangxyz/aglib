/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageCompatibility
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TripleNatTransComparison

/-! # The original open outer-adjoint map retains its native derived unit

No invertibility of `j! → Rj*` is presumed. Source and target native models
are explicit and independent.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dU dX
variable (Λ : Type (u + 1)) [Ring Λ] {U X : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual ordinary module extension/inverse/direct-image adjoint triple. -/
def moduleOpenTriple :
    Adjunction.Triple (moduleLowerShriek j Λ) (moduleInverseImage j Λ)
      (moduleDirectImage j Λ) :=
  ⟨moduleLowerShriekAdjunction j Λ, moduleInverseImageAdjunction j Λ⟩

/-- The actual ordinary outer-adjoint map, before deriving. -/
abbrev moduleLowerShriekToDirectImage := (moduleOpenTriple Λ j).leftToRight

variable (hU : HasDerivedCategory.{dU} (ModuleSheaf U Λ))
  (hX : HasDerivedCategory.{dX} (ModuleSheaf X Λ))

/-- The same original canonical derived map has the original termwise derived-unit equation. -/
theorem moduleDerivedLowerShriekToDirectImage_unit (K : CochainComplex.Plus (ModuleSheaf U Λ)) :
    (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hU hX (moduleLowerShriek j Λ) _ _).app K ≫
      (@moduleDerivedLowerShriekToDirectImage Λ _ U X j _ hU hX).app
        ((@DerivedCategory.Plus.Q _ _ _ hU).obj K) =
    (@DerivedCategory.Plus.Q _ _ _ hX).map
        ((NatTrans.mapCochainComplexPlus (moduleLowerShriekToDirectImage Λ j)).app K) ≫
      (@rightDerivedFunctorPlusUnit _ _ _ _ _ _ hU hX (moduleDirectImage j Λ) _ _).app K :=
  @Adjunction.Triple.rightDerivedFunctorPlus_leftToRight_unit
    (ModuleSheaf U Λ) _ _ hU _ (ModuleSheaf X Λ) _ _ hX _
    (moduleLowerShriek j Λ) (moduleDirectImage j Λ) (moduleInverseImage j Λ)
    _ _ _ _ _ _ _ (moduleOpenTriple Λ j) (moduleLowerShriekToDirectImage Λ j)
    (moduleOpenTriple Λ j).leftToRight_app_map_adj₁_unit_app K

end AlgebraicGeometry.Scheme.EtaleCohomology
