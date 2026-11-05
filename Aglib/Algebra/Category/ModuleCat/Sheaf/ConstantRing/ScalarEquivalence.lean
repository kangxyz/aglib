/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ScalarUnit
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying
public import Aglib.Algebra.Category.ModuleCat.Sheaf.RingedScalarAction
public import Aglib.Algebra.Category.ModuleCat.ForgetAction

/-! # Original coefficient equivalences preserve noncentral scalar actions

These statements concern the specified underlying comparisons and original
module structures, not a replacement action on an isomorphic additive object.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace ModuleCat.Sheaf.ConstantRing
universe u v r w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ]
  [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Original forward comparison intertwines the native scalar section and scalar. -/
theorem moduleSheafUnderlyingIso_hom_smul
    (F : ModuleValuedSheaf.{u, v, r, w} J Λ) (U : Cᵒᵖ) (a : Λ)
    (x : ((moduleSheafEquivalence J Λ).functor.obj F).val.obj U) :
    (((moduleSheafUnderlyingIso J Λ).hom.app F).hom.app U)
        ((constantRingUnit J Λ).app U a • x) =
      a • (show F.obj.obj U from
        (((moduleSheafUnderlyingIso J Λ).hom.app F).hom.app U) x) := by
  exact constantModuleSheafificationUnderlyingIso_hom_smul J Λ
    ((constantSheafEquivalence J Λ).functor.obj F) U a x

/-- Original inverse comparison intertwines the scalar and native scalar section. -/
theorem moduleSheafInverseUnderlyingIso_hom_smul
    (M : ModuleSheaf.{u, v, r, w} J Λ) (U : Cᵒᵖ) (a : Λ)
    (x : ((moduleSheafEquivalence J Λ).inverse.obj M).obj.obj U) :
    (((moduleSheafInverseUnderlyingIso J Λ).hom.app M).hom.app U) (a • x) =
      (constantRingUnit J Λ).app U a • (show M.val.obj U from
        (((moduleSheafInverseUnderlyingIso J Λ).hom.app M).hom.app U) x) := by
  rw [moduleSheafInverseUnderlyingIso_hom_app]
  rfl

/-- The whole original forward comparison is scalar-equivariant. -/
theorem moduleSheafUnderlyingIso_scalar (a : Λ) :
    Functor.whiskerLeft (moduleSheafEquivalence J Λ).functor
        (SheafOfModules.underlyingScalarSection
          (constantRing J Λ) (constantRingUnit J Λ) a) ≫
      (moduleSheafUnderlyingIso J Λ).hom =
    (moduleSheafUnderlyingIso J Λ).hom ≫
      sheafCompose_map J (ModuleCat.forgetScalar Λ a) := by
  ext F U x
  exact moduleSheafUnderlyingIso_hom_smul J Λ F U a x

/-- The whole original inverse comparison is scalar-equivariant. -/
theorem moduleSheafInverseUnderlyingIso_scalar (a : Λ) :
    Functor.whiskerLeft (moduleSheafEquivalence J Λ).inverse
        (sheafCompose_map J (ModuleCat.forgetScalar Λ a)) ≫
      (moduleSheafInverseUnderlyingIso J Λ).hom =
    (moduleSheafInverseUnderlyingIso J Λ).hom ≫
      SheafOfModules.underlyingScalarSection
        (constantRing J Λ) (constantRingUnit J Λ) a := by
  ext M U x
  exact moduleSheafInverseUnderlyingIso_hom_smul J Λ M U a x

end ModuleCat.Sheaf.ConstantRing
