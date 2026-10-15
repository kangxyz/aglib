/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # The original scalar-extension mate on native open cohomology

The actual geometric open-Ext map, with its actual coefficient arrow, is
semilinear over compatible structural rings. Its transpose under the native
scalar adjunction gives the tensor transformation. Original-unit formulas
and the whole-space comparison identify it with the original tensor map on
the unchanged `Sheaf.H`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
  (p : Y ⟶ X) (σ : R →+* S)
  (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
  (h : p.appTop.hom.comp α = β.comp σ)
  {M : X.Modules} {N : Y.Modules}
  (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (n : ℕ)

include h in
/-- The original geometric map respects the actual coefficient multiplication defining
the structural scalar actions. -/
theorem moduleHPrimeGeometricMap_smul (U : X.Opensᵒᵖ) (r : R)
    (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U.unop) :
    (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback p φ) n).app U
      (((Sheaf.cohomologyPresheafFunctor.{u + 1} (Opens.grothendieckTopology X) n).map
        (moduleScalarOfGlobal X M (α r))).app U x) =
      ((Sheaf.cohomologyPresheafFunctor.{u + 1} (Opens.grothendieckTopology Y) n).map
        (moduleScalarOfGlobal Y N (β (σ r)))).app (op (p ⁻¹ᵁ U.unop))
          ((zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
            (moduleCoefficientPullback p φ) n).app U x) := by
  have hr : p.appTop (α r) = β (σ r) := DFunLike.congr_fun h r
  rw [← hr]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (zariskiCohomologyOpenMap_coefficients p
      (moduleCoefficientPullback p φ) (moduleCoefficientPullback p φ)
      (moduleScalarOfGlobal X M (α r)) (moduleScalarOfGlobal Y N (p.appTop (α r)))
      (moduleCoefficientPullback_scalar p φ (α r)) n) U) x

/-- The original geometric open-cohomology map, after actual structural scalar restriction. -/
def moduleHPrimeRestrictionMap :
    moduleHPrimePresheaf X α M n ⟶
      ((Opens.map p.base).op ⋙ moduleHPrimePresheaf Y β N n) ⋙
        ModuleCat.restrictScalars σ where
  app U := by
    letI := moduleHPrimeModuleOfHom X α M n U.unop
    letI := moduleHPrimeModuleOfHom Y β N n (p ⁻¹ᵁ U.unop)
    exact ModuleCat.ofHom
      (X := (moduleHPrimePresheaf X α M n).obj U)
      (Y := (ModuleCat.restrictScalars σ).obj
        (((Opens.map p.base).op ⋙ moduleHPrimePresheaf Y β N n).obj U)) {
      __ := ((zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback p φ) n).app U).hom
      map_smul' := fun r x => moduleHPrimeGeometricMap_smul p σ α β h φ n U r x }
  naturality U V i := by
    apply (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map_injective
    exact (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
      (moduleCoefficientPullback p φ) n).naturality i

/-- The native scalar-adjunction transpose of the original geometric open-cohomology map. -/
def moduleHPrimeTensorMap :
    moduleHPrimePresheaf X α M n ⋙ ModuleCat.extendScalars σ ⟶
      (Opens.map p.base).op ⋙ moduleHPrimePresheaf Y β N n :=
  (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).whiskerRight X.Opensᵒᵖ).homEquiv
    _ _).symm (moduleHPrimeRestrictionMap p σ α β h φ n)

/-- The actual open-cohomology tensor mate retains the original scalar adjunction unit. -/
theorem moduleHPrimeTensorMap_unit (U : X.Opensᵒᵖ) :
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).unit.app
        ((moduleHPrimePresheaf X α M n).obj U) ≫
      (ModuleCat.restrictScalars σ).map ((moduleHPrimeTensorMap p σ α β h φ n).app U) =
        (moduleHPrimeRestrictionMap p σ α β h φ n).app U := by
  have H := Equiv.apply_symm_apply
    (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).whiskerRight X.Opensᵒᵖ).homEquiv _ _)
    (moduleHPrimeRestrictionMap p σ α β h φ n)
  rw [Adjunction.homEquiv_apply] at H
  have HU := congrArg (fun k => k.app U) H
  simpa only [moduleHPrimeTensorMap, NatTrans.comp_app,
    Adjunction.whiskerRight_unit_app_app, Functor.id_obj,
    Functor.whiskeringRight_obj_map, Functor.whiskeringRight_obj_obj,
    Functor.whiskerRight_app] using HU

/-- A unit pure tensor is sent by the original native geometric map on the actual open. -/
theorem moduleHPrimeTensorMap_one_tmul (U : X.Opensᵒᵖ)
    (x : (moduleHPrimePresheaf X α M n).obj U) :
    (moduleHPrimeTensorMap p σ α β h φ n).app U ((1 : S) ⊗ₜ[R,σ] x) =
      (zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback p φ) n).app U x :=
  congrArg (fun k => k x) (moduleHPrimeTensorMap_unit p σ α β h φ n U)

/-- At the whole space the original open-cohomology tensor mate is the original
`Sheaf.H` tensor mate under the unchanged structural linear comparisons. -/
theorem moduleHPrimeTensorMap_top :
    letI := moduleHPrimeModuleOfHom X α M n ⊤
    letI := moduleHPrimeModuleOfHom Y β N n ⊤
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom Y β N n
    (moduleHPrimeTensorMap p σ α β h φ n).app (op ⊤) ≫
        (moduleHPrimeTopLinearEquivOfHom Y β N n).toModuleIso.hom =
      (ModuleCat.extendScalars σ).map
          (moduleHPrimeTopLinearEquivOfHom X α M n).toModuleIso.hom ≫
        moduleCohomologyTensorMap p σ α β h φ n := by
  let := moduleHPrimeModuleOfHom X α M n ⊤
  let := moduleHPrimeModuleOfHom Y β N n ⊤
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β N n
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change moduleHPrimeTopLinearEquivOfHom Y β N n
      ((moduleHPrimeTensorMap p σ α β h φ n).app (op ⊤) ((1 : S) ⊗ₜ[R,σ] x)) =
    moduleCohomologyTensorMap p σ α β h φ n
      ((ModuleCat.extendScalars σ).map
        (moduleHPrimeTopLinearEquivOfHom X α M n).toModuleIso.hom ((1 : S) ⊗ₜ[R,σ] x))
  erw [ModuleCat.ExtendScalars.map_tmul, moduleHPrimeTensorMap_one_tmul,
    moduleCohomologyTensorMap_one_tmul]
  exact sheafHPrimeTopAddEquiv_geometric p (moduleAddSheaf X M) (moduleAddSheaf Y N)
    (moduleCoefficientPullback p φ) n x

/-- Invertibility at the whole space is exactly invertibility of the original global tensor map. -/
theorem moduleHPrimeTensorMap_top_isIso_iff :
    IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op ⊤)) ↔
      IsIso (moduleCohomologyTensorMap p σ α β h φ n) := by
  let := moduleHPrimeModuleOfHom X α M n ⊤
  let := moduleHPrimeModuleOfHom Y β N n ⊤
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β N n
  constructor
  · intro H
    have : IsIso ((ModuleCat.extendScalars σ).map
        (moduleHPrimeTopLinearEquivOfHom X α M n).toModuleIso.hom ≫
          moduleCohomologyTensorMap p σ α β h φ n) := by
      rw [← moduleHPrimeTensorMap_top p σ α β h φ n]
      infer_instance
    exact IsIso.of_isIso_comp_left ((ModuleCat.extendScalars σ).map
      (moduleHPrimeTopLinearEquivOfHom X α M n).toModuleIso.hom)
        (moduleCohomologyTensorMap p σ α β h φ n)
  · intro H
    have : IsIso ((moduleHPrimeTensorMap p σ α β h φ n).app (op ⊤) ≫
        (moduleHPrimeTopLinearEquivOfHom Y β N n).toModuleIso.hom) := by
      rw [moduleHPrimeTensorMap_top p σ α β h φ n]
      infer_instance
    exact IsIso.of_isIso_comp_right ((moduleHPrimeTensorMap p σ α β h φ n).app (op ⊤))
      (moduleHPrimeTopLinearEquivOfHom Y β N n).toModuleIso.hom

end AlgebraicGeometry.Scheme.Cohomology
