/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Bilinear
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Chart

/-! # The original tensor section map on affine opens

For arbitrary quasicoherent module sheaves, the original sectionwise tensor map
is invertible on every affine open. The proof uses the canonical native tilde
tensor comparison on a spectrum, followed by the original affine chart and tensor
restriction maps. The resulting isomorphism has literally the original
`moduleTensorSectionLinear` as its forward map. Neither factor is assumed flat
or finite, and the scheme need not be separated or Noetherian.
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
variable {R : CommRingCat.{u}}

private def moduleTensorSpecGlobalSectionsIso (E F : (Spec R).Modules)
    [E.IsQuasicoherent] [F.IsQuasicoherent] :
    (moduleSpecΓFunctor (R := R)).obj E ⊗ (moduleSpecΓFunctor (R := R)).obj F ≅
      (moduleSpecΓFunctor (R := R)).obj ((moduleTensorLeftFunctor (Spec R) E).obj F) := by
  letI : IsIso E.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent (R := R) E
  letI : IsIso F.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent (R := R) F
  exact tilde.isoTop
    ((moduleSpecΓFunctor (R := R)).obj E ⊗ (moduleSpecΓFunctor (R := R)).obj F) ≪≫
      (moduleSpecΓFunctor (R := R)).mapIso
        (tildeTensorIso ((moduleSpecΓFunctor (R := R)).obj E)
          ((moduleSpecΓFunctor (R := R)).obj F)).symm ≪≫
      (moduleSpecΓFunctor (R := R)).mapIso
        (tensorSheafIso (Spec R) (asIso E.fromTildeΓ) (asIso F.fromTildeΓ))

private theorem moduleTensorSpecGlobalSectionsIso_hom_tmul (E F : (Spec R).Modules)
    [E.IsQuasicoherent] [F.IsQuasicoherent]
    (e : Γ(E, ⊤)) (f : Γ(F, ⊤)) :
    (moduleTensorSpecGlobalSectionsIso E F).hom (e ⊗ₜ[R] f) =
      moduleTensorSection (Spec R) E F ⊤ e f := by
  let A := (moduleSpecΓFunctor (R := R)).obj E
  let B := (moduleSpecΓFunctor (R := R)).obj F
  let t := (moduleSpecΓFunctor (R := R)).mapIso (tildeTensorIso A B)
  have ht : t.hom
      ((tensorSheafUnit (Spec R) (tilde A) (tilde B)).app (op ⊤)
        ((show Γ(tilde A, ⊤) from tilde.toOpen A ⊤ e) ⊗ₜ
          (show Γ(tilde B, ⊤) from tilde.toOpen B ⊤ f))) =
        tilde.toOpen (A ⊗ B) ⊤ (e ⊗ₜ[R] f) :=
    tildeTensorIso_hom_tmul A B ⊤ e f
  have ht' : t.inv (tilde.toOpen (A ⊗ B) ⊤ (e ⊗ₜ[R] f)) =
      (tensorSheafUnit (Spec R) (tilde A) (tilde B)).app (op ⊤)
        ((show Γ(tilde A, ⊤) from tilde.toOpen A ⊤ e) ⊗ₜ
          (show Γ(tilde B, ⊤) from tilde.toOpen B ⊤ f)) := by
    have h := congrArg (fun z ↦ t.inv z) ht
    simpa only [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply] using h.symm
  change (tensorSheafMap (Spec R) E.fromTildeΓ F.fromTildeΓ).val.app (op ⊤)
    (t.inv (tilde.toOpen (A ⊗ B) ⊤ (e ⊗ₜ[R] f))) = _
  erw [ht', tensorSheafMap_tmul]
  have hE := congrArg (fun q ↦ q e) (toOpen_fromTildeΓ_app E ⊤)
  have hF := congrArg (fun q ↦ q f) (toOpen_fromTildeΓ_app F ⊤)
  change E.fromTildeΓ.val.app (op ⊤) (tilde.toOpen A ⊤ e) =
    ((modulesSpecToSheaf.obj E).presheaf.map (𝟙 (op ⊤))) e at hE
  erw [CategoryTheory.Functor.map_id] at hE
  simp only [ModuleCat.id_apply] at hE
  change F.fromTildeΓ.val.app (op ⊤) (tilde.toOpen B ⊤ f) =
    ((modulesSpecToSheaf.obj F).presheaf.map (𝟙 (op ⊤))) f at hF
  erw [CategoryTheory.Functor.map_id] at hF
  simp only [ModuleCat.id_apply] at hF
  rw [hE, hF]
  rfl


private theorem moduleSpecΓFunctor_map_apply {M N : (Spec R).Modules}
    (f : M ⟶ N) (m : Γ(M, ⊤)) :
    ((moduleSpecΓFunctor (R := R)).map f) m = f.val.app (op ⊤) m := rfl

private theorem affineChartΓIso_hom_apply {X : Scheme.{u}}
    (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)
    (m : (moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec)) :
    (affineChartΓIso ⟨U, hU⟩ M).hom m =
      M.presheaf.map (eqToHom (show U = hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) by
        simp [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])).op m := rfl

private def moduleTensorAffineSectionsIso {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (E F : X.Modules) [E.IsQuasicoherent] [F.IsQuasicoherent] :
    ModuleCat.of Γ(X, U) Γ(E, U) ⊗ ModuleCat.of Γ(X, U) Γ(F, U) ≅
      ModuleCat.of Γ(X, U) Γ((moduleTensorLeftFunctor X E).obj F, U) :=
  tensorIso (affineChartΓIso ⟨U, hU⟩ E).symm (affineChartΓIso ⟨U, hU⟩ F).symm ≪≫
    moduleTensorSpecGlobalSectionsIso (R := Γ(X, U))
      (E.restrict hU.fromSpec) (F.restrict hU.fromSpec) ≪≫
      (moduleSpecΓFunctor (R := Γ(X, U))).mapIso (tensorRestrictionIso hU.fromSpec E F) ≪≫
        affineChartΓIso ⟨U, hU⟩ ((moduleTensorLeftFunctor X E).obj F)

private theorem affineChartΓIso_tensor_section {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (E F : X.Modules)
    (e : Γ(E.restrict hU.fromSpec, ⊤)) (f : Γ(F.restrict hU.fromSpec, ⊤)) :
    (affineChartΓIso ⟨U, hU⟩ ((moduleTensorLeftFunctor X E).obj F)).hom
      (((moduleSpecΓFunctor (R := Γ(X, U))).map
        (tensorRestrictionIso hU.fromSpec E F).hom)
          (moduleTensorSection (Spec Γ(X, U)) (E.restrict hU.fromSpec)
            (F.restrict hU.fromSpec) ⊤ e f)) =
      moduleTensorSection X E F U ((affineChartΓIso ⟨U, hU⟩ E).hom e)
        ((affineChartΓIso ⟨U, hU⟩ F).hom f) := by
  let j := hU.fromSpec
  let T := (moduleTensorLeftFunctor X E).obj F
  let h : U = j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := by
    simp [j, Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have hres := tensorRestrictionIso_section j E F ⊤ e f
  have hsec := moduleTensorSection_restrict E F (eqToHom h) e f
  have ht := (congrArg (fun z ↦ T.presheaf.map (eqToHom h).op z) hres).trans hsec
  let G := moduleSpecΓFunctor (R := Γ(X, U))
  let z := moduleTensorSection (Spec Γ(X, U)) (E.restrict j) (F.restrict j) ⊤ e f
  have hchart := affineChartΓIso_hom_apply U hU T
    ((G.map (tensorRestrictionIso j E F).hom) z)
  have hmap := moduleSpecΓFunctor_map_apply (R := Γ(X, U))
    (tensorRestrictionIso j E F).hom z
  have hinputs := congrArg₂ (moduleTensorSection X E F U)
    (affineChartΓIso_hom_apply U hU E e) (affineChartΓIso_hom_apply U hU F f)
  exact hchart.trans ((congrArg (fun w ↦ T.presheaf.map (eqToHom h).op w) hmap).trans
    (ht.trans hinputs.symm))

private theorem moduleTensorAffineSectionsIso_hom {X : Scheme.{u}}
    (U : X.Opens) (hU : IsAffineOpen U) (E F : X.Modules)
    [E.IsQuasicoherent] [F.IsQuasicoherent] :
    (moduleTensorAffineSectionsIso U hU E F).hom =
      ((affineChartΓIso ⟨U, hU⟩ E).inv ⊗ₘ (affineChartΓIso ⟨U, hU⟩ F).inv) ≫
        (moduleTensorSpecGlobalSectionsIso (R := Γ(X, U))
          (E.restrict hU.fromSpec) (F.restrict hU.fromSpec)).hom ≫
        (moduleSpecΓFunctor (R := Γ(X, U))).map (tensorRestrictionIso hU.fromSpec E F).hom ≫
        (affineChartΓIso ⟨U, hU⟩ ((moduleTensorLeftFunctor X E).obj F)).hom := rfl

private theorem moduleTensorAffineSectionsIso_hom_tmul {X : Scheme.{u}}
    (U : X.Opens) (hU : IsAffineOpen U)
    (E F : X.Modules) [E.IsQuasicoherent] [F.IsQuasicoherent]
    (e : Γ(E, U)) (f : Γ(F, U)) :
    (moduleTensorAffineSectionsIso U hU E F).hom (e ⊗ₜ[Γ(X, U)] f) =
      moduleTensorSection X E F U e f := by
  let j := hU.fromSpec
  let G := moduleSpecΓFunctor (R := Γ(X, U))
  let T := (moduleTensorLeftFunctor X E).obj F
  let e' := (affineChartΓIso ⟨U, hU⟩ E).inv e
  let f' := (affineChartΓIso ⟨U, hU⟩ F).inv f
  have hspec := moduleTensorSpecGlobalSectionsIso_hom_tmul (R := Γ(X, U))
    (E.restrict j) (F.restrict j) e' f'
  calc
    _ = (affineChartΓIso ⟨U, hU⟩ T).hom
        ((G.map (tensorRestrictionIso j E F).hom)
          ((moduleTensorSpecGlobalSectionsIso (R := Γ(X, U))
            (E.restrict j) (F.restrict j)).hom (e' ⊗ₜ[Γ(X, U)] f'))) := by
      rw [moduleTensorAffineSectionsIso_hom]
      rfl
    _ = (affineChartΓIso ⟨U, hU⟩ T).hom
        ((G.map (tensorRestrictionIso j E F).hom)
          (moduleTensorSection (Spec Γ(X, U)) (E.restrict j) (F.restrict j) ⊤ e' f')) :=
      congrArg (fun z ↦ (affineChartΓIso ⟨U, hU⟩ T).hom
        ((G.map (tensorRestrictionIso j E F).hom) z)) hspec
    _ = moduleTensorSection X E F U ((affineChartΓIso ⟨U, hU⟩ E).hom e')
        ((affineChartΓIso ⟨U, hU⟩ F).hom f') :=
      affineChartΓIso_tensor_section U hU E F e' f'
    _ = _ := congrArg₂ (moduleTensorSection X E F U)
      ((affineChartΓIso ⟨U, hU⟩ E).toLinearEquiv.apply_symm_apply e)
      ((affineChartΓIso ⟨U, hU⟩ F).toLinearEquiv.apply_symm_apply f)

/-- The original sheafification-unit tensor map is bijective on every affine open
for arbitrary quasicoherent factors. -/
theorem moduleTensorSectionLinear_bijective_of_isAffine {X : Scheme.{u}}
    (E F : X.Modules) [E.IsQuasicoherent] [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (moduleTensorSectionLinear X E F U) := by
  have heq : (moduleTensorAffineSectionsIso U hU E F).hom.hom =
      moduleTensorSectionLinear X E F U := by
    apply TensorProduct.ext'
    intro e f
    exact moduleTensorAffineSectionsIso_hom_tmul U hU E F e f
  have h := (moduleTensorAffineSectionsIso U hU E F).toLinearEquiv.bijective
  change Function.Bijective (moduleTensorAffineSectionsIso U hU E F).hom.hom at h
  rw [heq] at h
  exact h

/-- The original affine tensor section map is an isomorphism in its native
section-module category. -/
theorem moduleTensorSectionLinear_isIso_of_isAffine {X : Scheme.{u}}
    (E F : X.Modules) [E.IsQuasicoherent] [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (ModuleCat.ofHom (moduleTensorSectionLinear X E F U)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (moduleTensorSectionLinear_bijective_of_isAffine E F U hU)

/-- The native affine section isomorphism with the original tensor section map
as its forward arrow. -/
def moduleTensorSectionIso {X : Scheme.{u}}
    (E F : X.Modules) [E.IsQuasicoherent] [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ModuleCat.of Γ(X, U) Γ(E, U) ⊗ ModuleCat.of Γ(X, U) Γ(F, U) ≅
      ModuleCat.of Γ(X, U) Γ((moduleTensorLeftFunctor X E).obj F, U) := by
  letI := moduleTensorSectionLinear_isIso_of_isAffine E F U hU
  exact asIso (ModuleCat.ofHom (moduleTensorSectionLinear X E F U))

/-- The affine tensor section isomorphism retains each original pure-section generator. -/
theorem moduleTensorSectionIso_hom_tmul {X : Scheme.{u}}
    (E F : X.Modules) [E.IsQuasicoherent] [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (e : Γ(E, U)) (f : Γ(F, U)) :
    (moduleTensorSectionIso E F U hU).hom (e ⊗ₜ[Γ(X, U)] f) =
      moduleTensorSection X E F U e f := rfl

end AlgebraicGeometry.Scheme.Modules
