/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.Localization.Counit
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Localization

/-!
# The natural comparison between literal tensor scalar extension and actual module localization
over an arbitrary commutative ring.

Source: `lean/R5Lab/Aglib/Algebra/Category/ModuleCat/Localization/BaseChange.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `93ec42c0f76d10f0a6a9ed28dbb5ba92889dea5eb9bd6693a929ab6af145729c`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat
universe u

section ModuleComparison
open scoped TensorProduct ChangeOfRings

variable {R : Type u} [CommRing R] (S : Submonoid R)
/-- The actual tensor extension and actual module localization agree. -/
def tensorLocalizationIso (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M ≅
      M.localizedModule S :=
  extendScalarsAlgebraIso R (Localization S) M ≪≫
    (IsLocalizedModule.isBaseChange S (Localization S)
      (M.localizedModuleMkLinearMap S)).equiv.toModuleIso

/-- The tensor comparison preserves the actual localization map on pure tensors. -/
@[simp] theorem tensorLocalizationIso_hom_tmul (M : ModuleCat.{u} R)
    (s : Localization S) (m : M) :
    (tensorLocalizationIso S M).hom (s ⊗ₜ[R,algebraMap R (Localization S)] m) =
      s • M.localizedModuleMkLinearMap S m := by
  change (IsLocalizedModule.isBaseChange S (Localization S)
    (M.localizedModuleMkLinearMap S)).equiv
      ((extendScalarsAlgebraIso R (Localization S) M).hom
        (s ⊗ₜ[R,algebraMap R (Localization S)] m)) = _
  rw [extendScalarsAlgebraIso_tmul, IsBaseChange.equiv_tmul]


/-- The natural isomorphism from tensor extension to localization at `S`. -/
def tensorLocalizationNatIso :
    ModuleCat.extendScalars (algebraMap R (Localization S)) ≅
      ModuleCat.localizedModuleFunctor.{u} S :=
  NatIso.ofComponents (tensorLocalizationIso S) (by
    intro M N f
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (tensorLocalizationIso S N).hom
        ((extendScalars (algebraMap R (Localization S))).map f
          ((1 : Localization S) ⊗ₜ[R,algebraMap R (Localization S)] m)) =
      localizedModuleMap S f ((tensorLocalizationIso S M).hom
        ((1 : Localization S) ⊗ₜ[R,algebraMap R (Localization S)] m))
    rw [ExtendScalars.map_tmul, tensorLocalizationIso_hom_tmul,
      tensorLocalizationIso_hom_tmul, one_smul, one_smul]
    change N.localizedModuleMkLinearMap S (f m) =
      (IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
        (N.localizedModuleMkLinearMap S) (Localization S) f.hom)
          (M.localizedModuleMkLinearMap S m)
    rw [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply])

end ModuleComparison

end ModuleCat
