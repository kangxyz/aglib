/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.Stalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Torsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Basic

/-!
# Internal torsion under original open extension by zero

The original geometric stalk is unchanged inside the open and zero outside.
The existing geometric-stalk criterion therefore proves preservation of the
internal local-annihilator condition. The original scalar-forgetting comparison
transfers this fact to genuine constant-ring module sheaves. No uniform
annihilator, proper-base-change statement, or finiteness hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original open extension by zero preserves internally torsion abelian sheaves. -/
theorem IsTorsion.etaleLowerShriek {F : AbelianSheaf.{u, u + 1} U}
    (hF : IsTorsion U F) : IsTorsion X ((etaleLowerShriek j).obj F) := by
  apply isTorsion_of_geometricStalks
  intro Ω _ _ η
  by_cases hη : ∃ ζ : Spec (.of Ω) ⟶ U, ζ ≫ j = η
  · obtain ⟨ζ, rfl⟩ := hη
    let e := (etaleLowerShriekStalkIso j ζ).app F
    apply IsAddTorsion.of_surjective (f := e.inv.hom) ?_ (hF.geometricStalk ζ)
    intro z
    refine ⟨e.hom z, ?_⟩
    exact ConcreteCategory.congr_hom e.hom_inv_id z
  · have hz := isZero_etaleLowerShriek_stalk_of_no_lift j η
      (fun ζ hζ => hη ⟨ζ, hζ⟩) F
    have := AddCommGrpCat.subsingleton_of_isZero hz
    intro z
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    exact ⟨1, Nat.zero_lt_one, Subsingleton.elim _ _⟩

/-- Genuine module extension by zero preserves the original internal torsion condition. -/
theorem moduleIsTorsion_moduleLowerShriek (Λ : Type (u + 1)) [Ring Λ]
    {M : ModuleSheaf U Λ} (hM : moduleIsTorsion U Λ M) :
    moduleIsTorsion X Λ ((moduleLowerShriek j Λ).obj M) := by
  have h := IsTorsion.etaleLowerShriek j hM
  let e := (moduleLowerShriekUnderlyingIso j Λ).app M
  apply Presheaf.IsLocallyTorsion.of_injective h e.hom.hom
  intro V
  exact (((sheafToPresheaf (Scheme.smallEtaleTopology X)
    AddCommGrpCat.{u + 1}).mapIso e).app V).addCommGroupIsoToAddEquiv.injective

end AlgebraicGeometry.Scheme.EtaleCohomology
