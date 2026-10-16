/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Localization.Exactness
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Localization of a submodule inclusion

The actual localized inclusion of a submodule is an isomorphism when its localized underlying
submodule is the whole module.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/AffineApproximation.lean`.
SHA-256: `2029b40cd181d56164f97a019526a3e93de58da78ca2ad65b0f9b33ad9b3ef18`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat

/-- A finite submodule whose localization is the whole localized module has
an isomorphic localized inclusion. -/
theorem isIso_localized_subtype_of_eq_top (R : CommRingCat.{u}) (p : Submonoid R)
    (M : ModuleCat.{u} R) (L : Submodule R M)
    (hL : L.localized' (Localization p) p (M.localizedModuleMkLinearMap p) = ⊤) :
    IsIso (ModuleCat.localizedModuleMap p (ModuleCat.ofHom L.subtype)) := by
  let a : ModuleCat.of.{u} R L ⟶ M := ModuleCat.ofHom L.subtype
  have : Mono a := (ModuleCat.mono_iff_injective a).mpr Subtype.val_injective
  have : Mono (ModuleCat.localizedModuleMap p a) :=
    (ModuleCat.localizedModuleFunctor p).map_mono a
  have hloc : IsLocalizedModule p ((ModuleCat.of.{u} R L).localizedModuleMkLinearMap p) :=
    ModuleCat.localizedModule_isLocalizedModule _ _
  have : Epi (ModuleCat.localizedModuleMap p a) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    apply LinearMap.range_eq_top.mp
    change LinearMap.range (IsLocalizedModule.mapExtendScalars p
      ((ModuleCat.of.{u} R L).localizedModuleMkLinearMap p)
      (M.localizedModuleMkLinearMap p) (Localization p) L.subtype) = ⊤
    change LinearMap.range ((IsLocalizedModule.map p
      ((ModuleCat.of.{u} R L).localizedModuleMkLinearMap p)
      (M.localizedModuleMkLinearMap p) L.subtype).extendScalarsOfIsLocalization p
        (Localization p)) = ⊤
    rw [← LinearMap.localized'_range_eq_range_localizedMap (Localization p) p
      ((ModuleCat.of.{u} R L).localizedModuleMkLinearMap p) (M.localizedModuleMkLinearMap p)]
    simpa only [a, ModuleCat.hom_ofHom, Submodule.range_subtype] using hL
  exact isIso_of_mono_of_epi _

end ModuleCat
