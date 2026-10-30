/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Unit
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The unit module of a constant ring and its underlying sheaf

On a site with the displayed sheafifications and local-bijectivity comparisons,
the lifted unit of the original constant ring sheaf has underlying abelian sheaf
the constant abelian sheaf. The comparison sheafifies the original constant-ring
unit, followed by the sheafification counit. Its original section map and local
injectivity and surjectivity are retained before any scheme specialization.

Sources: Mathlib `Sites/LocallyBijective.lean`, `GrothendieckTopology.W_iff`;
the original construction in etale `Duality/ModuleUnitUnderlying.lean`.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [Ring Λ] [HasWeakSheafify J RingCat.{w}]

/-- The original lifted rank-one module over the constant ring sheaf. -/
abbrev moduleUnit : ModuleSheaf.{u, v, w, w} J Λ :=
  SheafOfModules.liftedUnit.{u, v, w, w} (constantRing J Λ)

/-- The presheaf map from the constant abelian presheaf `Λ` to the underlying abelian sheaf of
`Λ_X`: the original constant-ring unit `Λ → Λ_X(V)` on sections, followed by `ULift.up`. -/
def moduleUnitConstantMap :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of Λ) ⟶
      ((SheafOfModules.toSheaf (constantRing J Λ)).obj (moduleUnit J Λ)).obj where
  app V := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((constantRingUnit J Λ).app V).hom.toAddMonoidHom)
  naturality V W f := by
    ext a
    exact congrArg ULift.up (ConcreteCategory.congr_hom ((constantRingUnit J Λ).naturality f) a)

/-- The comparison of `moduleUnitConstantMap` with the original constant-ring unit after
forgetting to types: the identity of `Λ`, the unit, and `ULift.up`. -/
theorem moduleUnitConstantMap_whiskerRight_forget :
    Functor.whiskerRight (moduleUnitConstantMap J Λ)
        (CategoryTheory.forget AddCommGrpCat.{w}) =
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
          (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of Λ) ⋙
              CategoryTheory.forget AddCommGrpCat.{w} ≅
            (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⋙
              CategoryTheory.forget RingCat.{w}).hom ≫
        Functor.whiskerRight (constantRingUnit J Λ) (CategoryTheory.forget RingCat.{w}) ≫
          (NatIso.ofComponents (fun _ => (Equiv.ulift : ULift.{w, w} _ ≃ _).symm.toIso)
              (fun _ => rfl) :
            (constantRing J Λ).obj ⋙ CategoryTheory.forget RingCat.{w} ≅
              ((SheafOfModules.toSheaf (constantRing J Λ)).obj (moduleUnit J Λ)).obj ⋙
                CategoryTheory.forget AddCommGrpCat.{w}).hom := by
  ext V a
  rfl

variable [J.WEqualsLocallyBijective RingCat.{w}]

/-- The presheaf map `moduleUnitConstantMap` is locally injective. -/
theorem moduleUnitConstantMap_isLocallyInjective :
    Presheaf.IsLocallyInjective J (moduleUnitConstantMap J Λ) := by
  rw [← Presheaf.isLocallyInjective_forget_iff, moduleUnitConstantMap_whiskerRight_forget]
  infer_instance

/-- The presheaf map `moduleUnitConstantMap` is locally surjective. -/
theorem moduleUnitConstantMap_isLocallySurjective :
    Presheaf.IsLocallySurjective J (moduleUnitConstantMap J Λ) := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget, moduleUnitConstantMap_whiskerRight_forget]
  infer_instance

variable [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The sheafification of `moduleUnitConstantMap` is an isomorphism. -/
theorem moduleUnitConstantMap_presheafToSheaf_map_isIso :
    IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map
      (moduleUnitConstantMap J Λ)) := by
  have := moduleUnitConstantMap_isLocallyInjective J Λ
  have := moduleUnitConstantMap_isLocallySurjective J Λ
  exact (J.W_iff _).mp
    (J.W_of_isLocallyBijective _)

/-- The constant abelian sheaf `Λ` is the underlying abelian sheaf of `Λ_X`: the sheafification
of `moduleUnitConstantMap`, followed by the counit of the sheafification adjunction. -/
def moduleUnitUnderlyingIso :
    (constantSheaf J AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of Λ) ≅
      (SheafOfModules.toSheaf (constantRing J Λ)).obj (moduleUnit J Λ) :=
  @asIso _ _ _ _ ((presheafToSheaf J AddCommGrpCat.{w}).map
      (moduleUnitConstantMap J Λ)) (moduleUnitConstantMap_presheafToSheaf_map_isIso J Λ) ≪≫
    asIso ((sheafificationAdjunction J
      AddCommGrpCat.{w}).counit.app
        ((SheafOfModules.toSheaf (constantRing J Λ)).obj (moduleUnit J Λ)))


end ModuleCat.Sheaf.ConstantRing
