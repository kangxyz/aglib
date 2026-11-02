/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageIdentity
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TripleComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorization
/-! # The actual identity triple comparison across independent native models -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dE dM
variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})

/-- The original ordinary outer-adjoint identity comparison. -/
def moduleIdentityOuterIso : moduleLowerShriek (𝟙 X) Λ ≅ moduleDirectImage (𝟙 X) Λ :=
  moduleLowerShriekIdIso Λ X ≪≫ (moduleDirectImageIdIso Λ X).symm

/-- The original ordinary identity comparisons retain both original adjunction units. -/
theorem moduleIdentityOuterIso_unit (M : ModuleSheaf X Λ) :
    (moduleIdentityOuterIso Λ X).hom.app M ≫
      (moduleDirectImage (𝟙 X) Λ).map ((moduleLowerShriekAdjunction (𝟙 X) Λ).unit.app M) =
    (moduleInverseImageAdjunction (𝟙 X) Λ).unit.app ((moduleLowerShriek (𝟙 X) Λ).obj M) := by
  let t : Adjunction.Triple (moduleLowerShriek (𝟙 X) Λ) (moduleInverseImage (𝟙 X) Λ)
      (moduleDirectImage (𝟙 X) Λ) :=
    ⟨moduleLowerShriekAdjunction (𝟙 X) Λ, moduleInverseImageAdjunction (𝟙 X) Λ⟩
  have h := Adjunction.Triple.leftToRight_identity t (moduleLowerShriekIdIso Λ X)
    (moduleInverseImageIdIso Λ X) (moduleDirectImageIdIso Λ X)
    (conjugateEquiv_moduleLowerShriekIdIso_hom Λ X)
    (conjugateEquiv_moduleInverseImageIdIso_hom Λ X)
  change (moduleIdentityOuterIso Λ X).hom.app M ≫
    (moduleDirectImage (𝟙 X) Λ).map (t.adj₁.unit.app M) = t.adj₂.unit.app _
  rw [show (moduleIdentityOuterIso Λ X).hom = t.leftToRight from h.symm]
  rw [Adjunction.Triple.leftToRight_app, ← (moduleDirectImage (𝟙 X) Λ).map_inv,
    Category.assoc, ← (moduleDirectImage (𝟙 X) Λ).map_comp, IsIso.inv_hom_id]
  rw [(moduleDirectImage (𝟙 X) Λ).map_id]
  exact Category.comp_id _

variable (hE : HasDerivedCategory.{dE} (ModuleSheaf X Λ))
  (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ))

/-- Native deriving of the original identity outer-adjoint iso, with both models explicit. -/
def moduleDerivedIdentityOuterIso :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hE hM (moduleLowerShriek (𝟙 X) Λ) _ _) ≅
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hE hM (moduleDirectImage (𝟙 X) Λ) _ _) :=
  @Functor.rightDerivedFunctorPlusIso (ModuleSheaf X Λ) _ _ hE _
    (ModuleSheaf X Λ) _ _ hM (moduleLowerShriek (𝟙 X) Λ) _
    (moduleDirectImage (𝟙 X) Λ) _ (moduleIdentityOuterIso Λ X)

/-- The canonical original triple map equals the native derived original comparison. -/
theorem moduleDerivedLowerShriekToDirectImage_identity_models :
    @moduleDerivedLowerShriekToDirectImage Λ _ X X (𝟙 X) _ hE hM =
      (moduleDerivedIdentityOuterIso Λ X hE hM).hom :=
  @Adjunction.Triple.rightDerivedFunctorPlus_leftToRight
    (ModuleSheaf X Λ) _ _ hE _ (ModuleSheaf X Λ) _ _ hM _
    (moduleLowerShriek (𝟙 X) Λ) (moduleDirectImage (𝟙 X) Λ) (moduleInverseImage (𝟙 X) Λ)
    _ _ _ _ _ _ _
    ⟨moduleLowerShriekAdjunction (𝟙 X) Λ, moduleInverseImageAdjunction (𝟙 X) Λ⟩
    (moduleIdentityOuterIso Λ X) (moduleIdentityOuterIso_unit Λ X)
end AlgebraicGeometry.Scheme.EtaleCohomology
