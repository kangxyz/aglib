/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSheafification
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Tensor products of actual quasicoherent scheme modules

The original sectionwise tensor of two tilde modules has a compatible seed from
`M ⊗[R] N`. On every principal open this seed is the tensor of the original
localization maps, followed by the canonical localization change of tensor ring.
The resulting sheafification isomorphism retains its original pure-section formula
on every open. Affine restriction then proves quasicoherence of the actual sheaf
tensor on an arbitrary scheme, with no flatness or finiteness premise.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)

/-- The original sectionwise tensor presheaf of two native tilde modules. -/
abbrev tildeTensorPresheaf : (Spec R).PresheafOfModules :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := (Spec R).presheaf)
    (tilde M).val (tilde N).val

/-- The original pure-section seed, with the affine scalar action transported to `R`. -/
def tildeTensorSeedApp (U : (Spec R).Opens) :
    M ⊗ N ⟶ (affinePresheafModules (tildeTensorPresheaf M N)).obj (op U) :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun m n ↦ (show Γ(tilde M, U) from tilde.toOpen M U m) ⊗ₜ[Γ(Spec R, U)]
      (show Γ(tilde N, U) from tilde.toOpen N U n))
    (by intro m m' n; dsimp; rw [map_add, TensorProduct.add_tmul])
    (by
      intro r m n
      dsimp
      erw [(tilde.toOpen M U).hom.map_smul]
      change (r • (show Γ(tilde M, U) from tilde.toOpen M U m)) ⊗ₜ
        (show Γ(tilde N, U) from tilde.toOpen N U n) =
        (algebraMap R Γ(Spec R, U) r) •
          ((show Γ(tilde M, U) from tilde.toOpen M U m) ⊗ₜ[Γ(Spec R, U)]
            (show Γ(tilde N, U) from tilde.toOpen N U n))
      rw [TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul])
    (by intro m n n'; dsimp; rw [map_add, TensorProduct.tmul_add])
    (by
      intro r m n
      dsimp
      erw [(tilde.toOpen N U).hom.map_smul]
      change (show Γ(tilde M, U) from tilde.toOpen M U m) ⊗ₜ[Γ(Spec R, U)]
        (r • (show Γ(tilde N, U) from tilde.toOpen N U n)) =
        (algebraMap R Γ(Spec R, U) r) •
          ((show Γ(tilde M, U) from tilde.toOpen M U m) ⊗ₜ[Γ(Spec R, U)]
            (show Γ(tilde N, U) from tilde.toOpen N U n))
      rw [← IsScalarTower.algebraMap_smul Γ(Spec R, U) r
        (show Γ(tilde N, U) from tilde.toOpen N U n), TensorProduct.tmul_smul])


/-- The affine tensor seed sends a pure tensor to the original pure tensor of tilde sections. -/
@[simp] theorem tildeTensorSeedApp_tmul (U : (Spec R).Opens) (m : M) (n : N) :
    tildeTensorSeedApp M N U (m ⊗ₜ[R] n) =
      (show Γ(tilde M, U) from tilde.toOpen M U m) ⊗ₜ[Γ(Spec R, U)]
      (show Γ(tilde N, U) from tilde.toOpen N U n) := rfl

/-- The original pure-section seed commutes with every restriction map. -/
def tildeTensorSeed :
    (Functor.const (Spec R).Opensᵒᵖ).obj (M ⊗ N) ⟶
      affinePresheafModules (tildeTensorPresheaf M N) where
  app U := tildeTensorSeedApp M N U.unop
  naturality {U V} i := by
    change tildeTensorSeedApp M N V.unop = tildeTensorSeedApp M N U.unop ≫
      (affinePresheafModules (tildeTensorPresheaf M N)).map i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl


/-- On every principal open the original tensor seed is a localization map. -/
theorem tildeTensorSeed_isLocalized (r : R) :
    IsLocalizedModule.Away r
      ((tildeTensorSeed M N).app (op (PrimeSpectrum.basicOpen r))).hom := by
  let U := PrimeSpectrum.basicOpen r
  let f : M →ₗ[R] Γ(tilde M, U) := (tilde.toOpen M U).hom
  let g : N →ₗ[R] Γ(tilde N, U) := (tilde.toOpen N U).hom
  let e : TensorProduct R Γ(tilde M, U) Γ(tilde N, U) ≃ₗ[R]
      (affinePresheafModules (tildeTensorPresheaf M N)).obj (op U) :=
    (IsLocalization.moduleTensorEquiv (.powers r) Γ(Spec R, U)
      Γ(tilde M, U) Γ(tilde N, U)).symm.restrictScalars R
  change IsLocalizedModule.Away r (tildeTensorSeedApp M N U).hom
  have heq : (tildeTensorSeedApp M N U).hom =
      e.toLinearMap ∘ₗ TensorProduct.map f g := by
    apply TensorProduct.ext'
    intro m n
    rfl
  rw [heq]
  have hf : IsLocalizedModule.Away r f := by
    change IsLocalizedModule.Away r (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    infer_instance
  have hg : IsLocalizedModule.Away r g := by
    change IsLocalizedModule.Away r (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom
    infer_instance
  exact IsLocalizedModule.of_linearEquiv (.powers r) (TensorProduct.map f g) e

/-- The actual sheaf tensor of two tilde modules is tilde of their native module tensor. -/
def tildeTensorIso :
    (moduleTensorLeftFunctor (Spec R) (tilde M)).obj (tilde N) ≅ tilde (M ⊗ N) :=
  affineSheafificationTildeIso (tildeTensorPresheaf M N) (M ⊗ N)
    (tildeTensorSeed M N) (tildeTensorSeed_isLocalized M N)

/-- The tilde tensor comparison retains the original sheafified seed on every open. -/
theorem tildeTensorIso_seed (U : (Spec R).Opens) (t : TensorProduct R M N) :
    (tildeTensorIso M N).hom.val.app (op U)
      ((tensorSheafUnit (Spec R) (tilde M) (tilde N)).app (op U)
        (tildeTensorSeedApp M N U t)) = tilde.toOpen (M ⊗ N) U t := by
  apply TopCat.Presheaf.IsSheaf.section_ext (tilde (M ⊗ N)).isSheaf
  intro x hxU
  obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.2
  refine ⟨_, hrU, hxr, ?_⟩
  let i := (homOfLE hrU).op
  have hs := congrArg (fun f ↦ f t) ((tildeTensorSeed M N).naturality i)
  change tildeTensorSeedApp M N (PrimeSpectrum.basicOpen r) t =
    (tildeTensorPresheaf M N).map i (tildeTensorSeedApp M N U t) at hs
  erw [← PresheafOfModules.naturality_apply (tildeTensorIso M N).hom.val i,
    ← PresheafOfModules.naturality_apply
      (tensorSheafUnit (Spec R) (tilde M) (tilde N)) i]
  erw [← hs]
  exact affineSheafificationTildeIso_seed (tildeTensorPresheaf M N) (M ⊗ N)
    (tildeTensorSeed M N) (tildeTensorSeed_isLocalized M N) r t

/-- The native tilde tensor comparison sends each original pure-section generator
to its tilde section. -/
theorem tildeTensorIso_hom_tmul (U : (Spec R).Opens) (m : M) (n : N) :
    (tildeTensorIso M N).hom.val.app (op U)
      ((tensorSheafUnit (Spec R) (tilde M) (tilde N)).app (op U)
        ((show Γ(tilde M, U) from tilde.toOpen M U m) ⊗ₜ[Γ(Spec R, U)]
          (show Γ(tilde N, U) from tilde.toOpen N U n))) =
      tilde.toOpen (M ⊗ N) U (m ⊗ₜ[R] n) :=
  tildeTensorIso_seed M N U (m ⊗ₜ[R] n)

/-- The original tensor of arbitrary affine quasicoherent module sheaves is quasicoherent. -/
theorem isQuasicoherent_moduleTensorLeftFunctor_affine
    (E F : (Spec R).Modules) [E.IsQuasicoherent] [F.IsQuasicoherent] :
    ((moduleTensorLeftFunctor (Spec R) E).obj F).IsQuasicoherent := by
  let e := tensorSheafIso (Spec R) (asIso E.fromTildeΓ).symm
    (asIso F.fromTildeΓ).symm ≪≫
    tildeTensorIso (moduleSpecΓFunctor.obj E) (moduleSpecΓFunctor.obj F)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e.symm
    inferInstance

/-- The original tensor of quasicoherent module sheaves is quasicoherent on every scheme. -/
theorem isQuasicoherent_moduleTensorLeftFunctor {X : Scheme.{u}}
    (E F : X.Modules) [E.IsQuasicoherent] [F.IsQuasicoherent] :
    ((moduleTensorLeftFunctor X E).obj F).IsQuasicoherent := by
  apply QuasiCoherent.quasicoherent_of_affineCharts
  intro R j _
  let e := tensorRestrictionIso j E F
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (isQuasicoherent_moduleTensorLeftFunctor_affine (E.restrict j) (F.restrict j))

end AlgebraicGeometry.Scheme.Modules
