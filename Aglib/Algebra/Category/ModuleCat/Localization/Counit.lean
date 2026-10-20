/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Localization.BaseChange
public import Aglib.Algebra.Category.ModuleCat.BaseChange
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.CategoryTheory.Whiskering

/-!
# The localization counit and restriction-then-localization comparison with their actual scalar
actions.

Source: `lean/R5Lab/Aglib/Algebra/Category/ModuleCat/Localization/Counit.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `4591e2d88b6352c6b6f6068d4779efb6e259891d8efd696f614768fd1f6f2347`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

variable (S : Submonoid R) [IsLocalization S A]

/-- Actual extension after scalar restriction is the original module, for
localization. The A-action is retained, not merely an additive equivalence. -/
def localizationCounitIso (N : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap R A)).obj
      ((ModuleCat.restrictScalars (algebraMap R A)).obj N) ≅ N := by
  let M := (ModuleCat.restrictScalars (algebraMap R A)).obj N
  have : IsScalarTower R A M := ⟨fun r a m => by
    change (r • a) • m = (algebraMap R A r) • (a • m)
    rw [Algebra.smul_def, mul_smul]⟩
  exact extendScalarsAlgebraIso R A M ≪≫
    (IsLocalization.moduleLid S A M).toModuleIso

open scoped ChangeOfRings in
/-- The localization counit retains the original unit-pure-tensor formula. -/
@[simp] theorem localizationCounitIso_hom_one_tmul (N : ModuleCat.{u} A)
    (n : (restrictScalars (algebraMap R A)).obj N) :
    (localizationCounitIso S N).hom ((1 : A) ⊗ₜ[R,algebraMap R A] n) = n := by
  have : IsScalarTower R A ((restrictScalars (algebraMap R A)).obj N) :=
    ⟨fun r a m => by
      change (r • a) • m = (algebraMap R A r) • (a • m)
      rw [Algebra.smul_def, mul_smul]⟩
  change (IsLocalization.moduleLid S A ((restrictScalars (algebraMap R A)).obj N))
    ((extendScalarsAlgebraIso R A ((restrictScalars (algebraMap R A)).obj N)).hom
      ((1 : A) ⊗ₜ[R,algebraMap R A] n)) = n
  rw [extendScalarsAlgebraIso_tmul]
  change (1 : A) • n = n
  exact one_smul A n

/-- The isomorphism has the original scalar adjunction counit as its forward map. -/
theorem localizationCounitIso_hom_eq_counit (N : ModuleCat.{u} A) :
    (localizationCounitIso S N).hom =
      (extendRestrictScalarsAdj (algebraMap R A)).counit.app N := by
  apply ExtendScalars.hom_ext
  intro n
  rw [localizationCounitIso_hom_one_tmul,
    extendRestrictScalarsAdj_counit_app_apply_one_tmul]

/-- The localization counit is natural in the original module. -/
def localizationCounitNatIso :
    ModuleCat.restrictScalars (algebraMap R A) ⋙
      ModuleCat.extendScalars (algebraMap R A) ≅ 𝟭 (ModuleCat.{u} A) :=
  NatIso.ofComponents (localizationCounitIso S) (by
    intro N N' f
    rw [localizationCounitIso_hom_eq_counit, localizationCounitIso_hom_eq_counit]
    exact (extendRestrictScalarsAdj (algebraMap R A)).counit.naturality f)

/-- The canonical scalar-action triangle, before sheafification. -/
def restrictThenLocalizeIso {k : Type u} [CommRing k] (χ : A →+* k) :
    ModuleCat.restrictScalars (χ.comp (algebraMap R A)) ⋙
      ModuleCat.extendScalars (algebraMap R A) ≅ ModuleCat.restrictScalars χ :=
  Functor.isoWhiskerRight (ModuleCat.restrictScalarsComp (algebraMap R A) χ) _ ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft _ (localizationCounitNatIso S) ≪≫
  Functor.rightUnitor _

end ModuleCat
