/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Affine
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Affine
public import Aglib.RingTheory.Grassmannian.BaseChange
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.SpanSingleton

/-!
# Base change of the quotients of Grassmannian points

For `R : CommRingCat` and an `R`-algebra `A`, the module `A ⊗[R] R^n` has the basis
`tensorBasis A : j ↦ 1 ⊗ eⱼ`, so a point `N` of Mathlib's Grassmannian `G(k, A ⊗[R] R^n; A)` has the
quotient `pointQuot A N = tildeQuot (tensorBasis A) N : O^n ⟶ ((A ⊗[R] R^n) ⧸ N)~` on `Spec A`.
For an `R`-algebra map `f : A ⟶ B`, pulling `pointQuot A N` back along `Spec f` gives the quotient
of Mathlib's base change `Module.Grassmannian.map f N` (`pullback_pointQuot`): the comparison is
`tildePullbackIso` followed by the inverse of `baseChangeMkQQuotEquiv`, and the compatibility with
the quotient maps is checked on the free generators through `affinePullbackTildeIso_unitToUnit`.

This uses the component formula of Mathlib's `baseChangeMkQ`, the named premise
`Module.Grassmannian.BaseChangeMkQFormula` (supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits TensorProduct

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

variable {R : CommRingCat.{u}} {k n : ℕ}

/-- The basis `j ↦ 1 ⊗ eⱼ` of `A ⊗[R] R^n`, indexed by `ULift (Fin n)`. -/
def tensorBasis (A : CommAlgCat.{u} R) :
    Module.Basis (ULift.{u} (Fin n)) A (A ⊗[R] (Fin n → R)) :=
  ((Pi.basisFun R (Fin n)).baseChange A).reindex Equiv.ulift.symm

theorem tensorBasis_apply (A : CommAlgCat.{u} R) (j : ULift.{u} (Fin n)) :
    tensorBasis A j = (1 : A) ⊗ₜ[R] (Pi.single j.down 1 : Fin n → R) := by
  simp [tensorBasis]

/-- The quotient on `Spec A` of a point of Mathlib's Grassmannian functor over `A`. -/
abbrev pointQuot (A : CommAlgCat.{u} R) (N : Module.Grassmannian A (A ⊗[R] (Fin n → R)) k) :
    LocallyFreeQuotient (Spec (CommRingCat.of A)) k n :=
  tildeQuot (A := CommRingCat.of A) (tensorBasis A) N

/-- The free generator `ιFree j` followed by the quotient map of `tildeQuot b N` is `tilde` of
`a ↦ a • [b j]`. -/
theorem ιFree_comp_tildeQuot_π {A : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [Module A M]
    (b : Module.Basis (ULift.{u} (Fin n)) A M) (N : Module.Grassmannian A M k)
    (j : ULift.{u} (Fin n)) :
    SheafOfModules.ιFree j ≫ (tildeQuot b N).π =
      tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A (M ⧸ N.toSubmodule)
        (N.toSubmodule.mkQ (b j)))) := by
  rw [tildeQuot_π, ← tildeBasisIso_hom_basisPoint (ModuleCat.of A M) b j, Category.assoc,
    Iso.hom_inv_id_assoc, ← tilde.map_comp]
  congr 1

variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

-- `letI`/`haveI` inline the algebra structure `f.toAlgebra` used by Mathlib's `map`.
set_option linter.style.haveILetI false in
/-- **Base change of point quotients**: pulling the quotient of `N` back along `Spec f` gives
the quotient of Mathlib's base change `Module.Grassmannian.map f N`. -/
theorem pullback_pointQuot {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (N : Module.Grassmannian A (A ⊗[R] (Fin n → R)) k) :
    (pointQuot A N).pullback (Spec.map (CommRingCat.ofHom (f.hom : A →+* B))) ≈
      pointQuot B (Module.Grassmannian.map f.hom N) := by
  letI : Algebra A B := f.hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.hom.comp_algebraMap.symm
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (f.hom : A →+* B)
  let P : ModuleCat (CommRingCat.of A) :=
    ModuleCat.of A ((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule)
  let eL := Module.Grassmannian.baseChangeMkQQuotEquiv (B := B) N.toSubmodule
  have hN : LinearMap.ker (Module.Grassmannian.baseChangeMkQ B N.toSubmodule) =
      (Module.Grassmannian.map f.hom N).toSubmodule :=
    (Module.Grassmannian.map_toSubmodule f.hom N).symm
  let eMod : (ModuleCat.extendScalars φ.hom).obj P ≅ ModuleCat.of B ((B ⊗[R] (Fin n → R)) ⧸
      (Module.Grassmannian.map f.hom N).toSubmodule) :=
    eL.symm.toModuleIso ≪≫ (Submodule.quotEquivOfEq _ _ hN).toModuleIso
  let iso₁ : ((pointQuot A N).pullback (Spec.map φ)).obj ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj P) := (tildePullbackIso φ).app P
  let iso₂ : tilde ((ModuleCat.extendScalars φ.hom).obj P) ≅
      (pointQuot B (Module.Grassmannian.map f.hom N)).obj :=
    (tilde.functor (CommRingCat.of B)).mapIso eMod
  refine ⟨⟨iso₁ ≪≫ iso₂, ?_⟩⟩
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan
    (R := (Spec (CommRingCat.of B)).ringCatSheaf) (ULift.{u} (Fin n))) _ _ (fun j ↦ ?_)
  change SheafOfModules.ιFree j ≫ _ = SheafOfModules.ιFree j ≫ _
  rw [ιFree_comp_tildeQuot_π]
  rw [← cancel_epi (pullbackUnitIso (Spec.map φ)).hom]
  have h1 : (pullbackUnitIso (Spec.map φ)).hom ≫ SheafOfModules.ιFree j ≫
      (pullbackFreeIso (Spec.map φ) (ULift.{u} (Fin n))).inv =
      (Scheme.Modules.pullback (Spec.map φ)).map (SheafOfModules.ιFree j) := by
    rw [← cancel_mono (pullbackFreeIso (Spec.map φ) (ULift.{u} (Fin n))).hom, Category.assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ j).symm
  have h4 : SheafOfModules.ιFree j ≫ (pointQuot A N).π = tilde.map (ModuleCat.ofHom
      (LinearMap.toSpanSingleton A ((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule)
        (N.toSubmodule.mkQ (tensorBasis A j)))) :=
    ιFree_comp_tildeQuot_π (A := CommRingCat.of A) _ _ j
  rw [LocallyFreeQuotient.pullback_π, Category.assoc, reassoc_of% h1,
    ← CategoryTheory.Functor.map_comp_assoc, h4]
  let g : ModuleCat.of (CommRingCat.of A) (CommRingCat.of A) ⟶ P :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton A
      ((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) (N.toSubmodule.mkQ (tensorBasis A j)))
  have h2 : (Scheme.Modules.pullback (Spec.map φ)).map (tilde.map g) ≫
      (tildePullbackIso φ).hom.app P = (tildePullbackIso φ).hom.app _ ≫
        tilde.map ((ModuleCat.extendScalars φ.hom).map g) :=
    (tildePullbackIso φ).hom.naturality g
  rw [Iso.trans_hom]
  change _ ≫ ((tildePullbackIso φ).hom.app P ≫ iso₂.hom) = _
  rw [reassoc_of% h2]
  have h3 : (tildePullbackIso φ).hom.app (ModuleCat.of (CommRingCat.of A) (CommRingCat.of A)) ≫
      tilde.map (ModuleCat.scalarExtensionUnit φ) = (pullbackUnitIso (Spec.map φ)).hom :=
    Scheme.Hom.affinePullbackTildeIso_unitToUnit φ
  rw [← h3, Category.assoc]
  congr 1
  change tilde.map _ ≫ tilde.map eMod.hom = _
  rw [← tilde.map_comp, ← tilde.map_comp]
  congr 1
  have hb : eL (Submodule.Quotient.mk (tensorBasis B j)) =
      (1 : B) ⊗ₜ[A] N.toSubmodule.mkQ (tensorBasis A j) := by
    rw [Module.Grassmannian.baseChangeMkQQuotEquiv_mk, tensorBasis_apply, tensorBasis_apply,
      Module.Grassmannian.baseChangeMkQ_tmul]
  have eL' : eL.symm ((1 : B) ⊗ₜ[A] N.toSubmodule.mkQ (tensorBasis A j)) =
      Submodule.Quotient.mk (tensorBasis B j) :=
    (LinearEquiv.symm_apply_eq eL).mpr hb.symm
  refine ModuleCat.extendScalars_map_toSpanSingleton_comp φ _ _ eMod.hom ?_
  exact (congrArg (Submodule.quotEquivOfEq _ _ hN) eL').trans
    (Submodule.quotEquivOfEq_mk _ _ hN _)

end AlgebraicGeometry.Grassmannian
