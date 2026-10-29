/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Coefficient
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The underlying abelian sheaf of the rank-one module sheaf

Let `X` be a scheme and `Λ` a ring. The underlying abelian sheaf of the rank-one module sheaf
`Λ_X = moduleUnit X Λ` (sections `ULift (Λ_X(V))`, Duality/ModuleCohomology) is the constant
abelian sheaf with value `Λ` (`moduleUnitUnderlyingIso`). The comparison is induced, through the
sheafification adjunction, by the original constant-ring unit `Λ → Λ_X(V)` on sections
(`moduleUnitConstantMap`); this presheaf map is locally injective and locally surjective because
the constant-ring unit is (`constantRingUnit_isLocallyInjective`, `_isLocallySurjective`), so its
sheafification is an isomorphism (Mathlib's `GrothendieckTopology.W_iff`, with
`WEqualsLocallyBijective` for abelian sheaves on the small étale site).

For `Λ = ULift (ZMod n)`, `moduleUnitCoefficientIso` identifies the underlying abelian sheaf of
`Λ_X` with the constant coefficient `ConstantFinite.coefficient (ULift (ZMod n)) X`, the constant
sheaf `ℤ/n` of the cohomology of curves. Through `moduleLowerShriekCohomologyAddEquiv` and
`CompactSupport.H.map`, the module group `H^r_c(U, Λ_U)` is then `H^r_c(U, ℤ/n)` of Milne,
*Lectures on Étale Cohomology* v2.21, Thm. 14.7, proof, Step 2, p. 94, for `F = ℤ/n`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The presheaf map from the constant abelian presheaf `Λ` to the underlying abelian sheaf of
`Λ_X`: the original constant-ring unit `Λ → Λ_X(V)` on sections, followed by `ULift.up`. -/
def moduleUnitConstantMap :
    (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of Λ) ⟶
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj (moduleUnit X Λ)).obj where
  app V := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((constantRingUnit X Λ).app V).hom.toAddMonoidHom)
  naturality V W f := by
    ext a
    exact congrArg ULift.up (ConcreteCategory.congr_hom ((constantRingUnit X Λ).naturality f) a)

/-- The comparison of `moduleUnitConstantMap` with the original constant-ring unit after
forgetting to types: the identity of `Λ`, the unit, and `ULift.up`. -/
theorem moduleUnitConstantMap_whiskerRight_forget :
    Functor.whiskerRight (moduleUnitConstantMap X Λ)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) =
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
          (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of Λ) ⋙
              CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
            (Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ) ⋙
              CategoryTheory.forget RingCat.{u + 1}).hom ≫
        Functor.whiskerRight (constantRingUnit X Λ) (CategoryTheory.forget RingCat.{u + 1}) ≫
          (NatIso.ofComponents (fun _ => (Equiv.ulift : ULift.{u + 1, u + 1} _ ≃ _).symm.toIso)
              (fun _ => rfl) :
            (constantRing X Λ).obj ⋙ CategoryTheory.forget RingCat.{u + 1} ≅
              ((SheafOfModules.toSheaf (constantRing X Λ)).obj (moduleUnit X Λ)).obj ⋙
                CategoryTheory.forget AddCommGrpCat.{u + 1}).hom := by
  ext V a
  rfl

/-- The presheaf map `moduleUnitConstantMap` is locally injective. -/
theorem moduleUnitConstantMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology X) (moduleUnitConstantMap X Λ) := by
  rw [← Presheaf.isLocallyInjective_forget_iff, moduleUnitConstantMap_whiskerRight_forget]
  infer_instance

/-- The presheaf map `moduleUnitConstantMap` is locally surjective. -/
theorem moduleUnitConstantMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology X) (moduleUnitConstantMap X Λ) := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget, moduleUnitConstantMap_whiskerRight_forget]
  infer_instance

/-- The sheafification of `moduleUnitConstantMap` is an isomorphism. -/
theorem moduleUnitConstantMap_presheafToSheaf_map_isIso :
    IsIso ((presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
      (moduleUnitConstantMap X Λ)) := by
  have := moduleUnitConstantMap_isLocallyInjective X Λ
  have := moduleUnitConstantMap_isLocallySurjective X Λ
  exact ((Scheme.smallEtaleTopology X).W_iff _).mp
    ((Scheme.smallEtaleTopology X).W_of_isLocallyBijective _)

/-- The constant abelian sheaf `Λ` is the underlying abelian sheaf of `Λ_X`: the sheafification
of `moduleUnitConstantMap`, followed by the counit of the sheafification adjunction. -/
def moduleUnitUnderlyingIso :
    (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of Λ) ≅
      (SheafOfModules.toSheaf (constantRing X Λ)).obj (moduleUnit X Λ) :=
  @asIso _ _ _ _ ((presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
      (moduleUnitConstantMap X Λ)) (moduleUnitConstantMap_presheafToSheaf_map_isIso X Λ) ≪≫
    asIso ((sheafificationAdjunction (Scheme.smallEtaleTopology X)
      AddCommGrpCat.{u + 1}).counit.app
        ((SheafOfModules.toSheaf (constantRing X Λ)).obj (moduleUnit X Λ)))

/-- For `ℤ/n`, the constant coefficient `ConstantFinite.coefficient (ULift (ZMod n)) X` is the
underlying abelian sheaf of `Λ_X`, `Λ = ULift (ZMod n)`. -/
def moduleUnitCoefficientIso (n : ℕ) :
    ConstantFinite.coefficient (ULift.{u} (ZMod n)) X ≅
      (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj
        (moduleUnit X (ULift.{u + 1} (ZMod n))) :=
  (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).mapIso
      (AddEquiv.ulift.trans (AddEquiv.ulift.trans AddEquiv.ulift.symm)).toAddCommGrpIso ≪≫
    moduleUnitUnderlyingIso X (ULift.{u + 1} (ZMod n))

end AlgebraicGeometry.Scheme.EtaleCohomology
