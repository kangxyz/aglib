/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.KernelBaseChange
public import Aglib.LinearAlgebra.TensorProduct.Map
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Chart
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction

/-!
# Actual kernels, sections and scalar-extended maps on affine schemes

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean`, SHA-256
  `0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/ZeroLocus.lean`, SHA-256
  `965a9542a747894891b7cc04c235143b80984b77c931144b0b17f93d36a2c820`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {M N : ModuleCat R}

/-- The kernel of a map between affine quasicoherent modules is represented by
its actual global-section kernel. The square is the tilde/Gamma counit square. -/
def affineQuasicoherentKernelIso {P Q : (Spec R).Modules}
    [P.IsQuasicoherent] [Q.IsQuasicoherent] (f : P ⟶ Q) :
    tilde (kernel ((moduleSpecΓFunctor (R := R)).map f)) ≅ kernel f :=
  PreservesKernel.iso (tilde.functor R) ((moduleSpecΓFunctor (R := R)).map f) ≪≫
    kernel.mapIso _ f (asIso P.fromTildeΓ) (asIso Q.fromTildeΓ)
      ((tilde.adjunction (R := R)).counit.naturality f)

/-- The actual kernel of a map between affine quasicoherent module sheaves is quasicoherent. -/
instance affineQuasicoherentKernel {P Q : (Spec R).Modules}
    [P.IsQuasicoherent] [Q.IsQuasicoherent] (f : P ⟶ Q) :
    (kernel f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (affineQuasicoherentKernelIso f) inferInstance

@[reassoc]
theorem affineQuasicoherentKernelIso_hom_ι {P Q : (Spec R).Modules}
    [P.IsQuasicoherent] [Q.IsQuasicoherent] (f : P ⟶ Q) :
    (affineQuasicoherentKernelIso f).hom ≫ kernel.ι f =
      tilde.map (kernel.ι ((moduleSpecΓFunctor (R := R)).map f)) ≫ P.fromTildeΓ := by
  simp only [affineQuasicoherentKernelIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι, asIso_hom]
  rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]
  rfl

end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u}) (M : (Spec R).Modules) [M.IsQuasicoherent]

theorem specSections_localized (s : R) :
    IsLocalizedModule (.powers s)
      (((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen s).leTop.op).hom) :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance s

end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules

theorem specModule_map_apply {R : CommRingCat.{u}} (M : (Spec R).Modules)
    {V W : (Spec R).Opens} (i : op V ⟶ op W) (a : Γ(M,V)) :
    (((modulesSpecToSheaf.obj M).obj.map i).hom) a = M.presheaf.map i a := rfl

theorem restriction_transport {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) {V W : X.Opens} (i : V ⟶ W)
    {V' W' : Y.Opens} (hv : V' = f ''ᵁ V) (hw : W' = f ''ᵁ W) (j : V' ⟶ W') :
    (M.restrict f).presheaf.map i.op ≫
      ((M.restrictAppIso f V) ≪≫ M.presheaf.mapIso (eqToIso hv).op).hom =
    ((M.restrictAppIso f W) ≪≫ M.presheaf.mapIso (eqToIso hw).op).hom ≫
      M.presheaf.map j.op := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    Scheme.Modules.map_restrictAppIso_hom_assoc, Category.assoc, ← Functor.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.affineOpens)
variable (M : X.Modules)
variable [M.IsQuasicoherent]

theorem affineSections_denominator (s : Γ(X,U)) (m : Γ(M,X.basicOpen s)) :
    ∃ (n : ℕ) (a : Γ(M,U)),
      (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s)^n • m =
        M.presheaf.map (homOfLE (X.basicOpen_le s)).op a := by
  let f : Spec Γ(X,U) ⟶ X := U.property.fromSpec
  let N : (Spec Γ(X,U)).Modules := M.restrict f
  let et : Γ(N,⊤) ≅ Γ(M,U) :=
    M.restrictAppIso f ⊤ ≪≫ M.presheaf.mapIso (eqToIso (by
      simp [f, Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec])).op
  let es : Γ(N,PrimeSpectrum.basicOpen s) ≅ Γ(M,X.basicOpen s) :=
    M.restrictAppIso f _ ≪≫ M.presheaf.mapIso
      (eqToIso (U.property.fromSpec_image_basicOpen s).symm).op
  let := specSections_localized Γ(X,U) N s
  obtain ⟨n, a, ha⟩ := IsLocalizedModule.Away.surj
    (((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen s).leTop.op).hom) s (es.inv m)
  refine ⟨n, et.hom a, ?_⟩
  have hsmul (r : Γ(X,U)) (z : Γ(N,PrimeSpectrum.basicOpen s)) :
      es.hom (r • z) = X.presheaf.map (homOfLE (X.basicOpen_le s)).op r • es.hom z := by
    dsimp only [es, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    simp only [ConcreteCategory.comp_apply]
    rw [affineChart_restrict_smul U M, M.map_smul]
    simp only [← Functor.map_comp_apply]
    rfl
  have hr := restriction_transport f M (PrimeSpectrum.basicOpen s).leTop
    (U.property.fromSpec_image_basicOpen s).symm
    (show U.val = f ''ᵁ (⊤ : (Spec Γ(X,U)).Opens) from by
      simp [f, Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec])
    (homOfLE (X.basicOpen_le s))
  have h := congrArg es.hom ha
  rw [hsmul, Iso.inv_hom_id_apply] at h
  have hr' := congrArg (fun k : Γ(N,⊤) ⟶ Γ(M,X.basicOpen s) ↦ k a) hr
  have h' : (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s)^n • m =
      es.hom (N.presheaf.map (PrimeSpectrum.basicOpen s).leTop.op a) := by
    simpa only [map_pow, specModule_map_apply] using h
  exact h'.trans hr'

end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules

open scoped ChangeOfRings

/-- For quasi-coherent modules on affine schemes, monicity of the actual
pullback implies monicity of scalar extension of the actual global-section map. -/
theorem affinePullback_extendScalars_mono {R S : CommRingCat.{u}} (α : R ⟶ S)
    {M N : (Spec R).Modules} [M.IsQuasicoherent]
    (φ : M ⟶ N) [Mono ((Scheme.Modules.pullback (Spec.map α)).map φ)] :
    Mono ((ModuleCat.extendScalars α.hom).map ((moduleSpecΓFunctor (R := R)).map φ)) := by
  let F := Scheme.Modules.pullback (Spec.map α)
  let ψ := (moduleSpecΓFunctor (R := R)).map φ
  have hc : tilde.map ψ ≫ N.fromTildeΓ = M.fromTildeΓ ≫ φ :=
    Scheme.Modules.fromTildeΓNatTrans.naturality φ
  have hfc : F.map (tilde.map ψ) ≫ F.map N.fromTildeΓ = F.map M.fromTildeΓ ≫ F.map φ := by
    simpa only [Functor.map_comp] using congrArg F.map hc
  have : Mono (F.map (tilde.map ψ) ≫ F.map N.fromTildeΓ) := by
    rw [hfc]
    infer_instance
  have : Mono (F.map (tilde.map ψ)) := mono_of_mono _ (F.map N.fromTildeΓ)
  have hn := ((tildePullbackIso α).hom.naturality ψ)
  have : Mono ((((tildePullbackIso α).app ((moduleSpecΓFunctor (R := R)).obj M))).hom ≫
      tilde.map ((ModuleCat.extendScalars α.hom).map ψ)) := by
    erw [← hn]
    change Mono (F.map (tilde.map ψ) ≫ (tildePullbackIso α).hom.app _)
    infer_instance
  have : Mono (tilde.map ((ModuleCat.extendScalars α.hom).map ψ)) :=
    (mono_comp_iff_of_isIso (((tildePullbackIso α).app ((moduleSpecΓFunctor (R := R)).obj M))).hom
      _).mp inferInstance
  exact (tilde.functor S).mono_of_mono_map this

/-- In native tensor-product terms, affine pullback monicity gives injectivity
of the global-section map after scalar extension. -/
theorem affinePullback_baseChange_injective (R T : Type u) [CommRing R] [CommRing T]
    [Algebra R T] {M N : (Spec (.of R)).Modules}
    [M.IsQuasicoherent] (φ : M ⟶ N)
    [Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).map φ)] :
    Function.Injective (((moduleSpecΓFunctor (R := .of R)).map φ).hom.baseChange T) := by
  let ψ := (moduleSpecΓFunctor (R := .of R)).map φ
  have : Mono ((ModuleCat.extendScalars (algebraMap R T)).map ψ) :=
    affinePullback_extendScalars_mono (CommRingCat.ofHom (algebraMap R T)) φ
  have h := ModuleCat.extendScalarsAlgebraIso_naturality R T ψ
  have : Mono ((ModuleCat.extendScalarsAlgebraIso R T _).hom ≫ ModuleCat.ofHom (ψ.hom.baseChange T))
    := by
    rw [← h]
    infer_instance
  have : Mono (ModuleCat.ofHom (ψ.hom.baseChange T)) :=
    (mono_comp_iff_of_isIso (ModuleCat.extendScalarsAlgebraIso R T ((moduleSpecΓFunctor (R := .of
      R)).obj M)).hom _).mp inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

/-- The affine chart sections comparison is natural for the actual module map. -/
theorem affineChartΓIso_naturality {X : Scheme.{u}} (U : X.affineOpens)
    {M N : X.Modules} (φ : M ⟶ N) :
    (moduleSpecΓFunctor (R := Γ(X, U))).map
        ((Scheme.Modules.restrictFunctor U.property.fromSpec).map φ) ≫
      (affineChartΓIso U N).hom =
    (affineChartΓIso U M).hom ≫ φ.val.app (op U.val) := by
  ext m
  dsimp [affineChartΓIso]
  change M.val.obj (op (U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))) at m
  let h : U.val = U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := by
    simp [Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec]
  change N.val.map (eqToHom h).op
      (φ.val.app (op (U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))) m) =
    φ.val.app (op U.val) (M.val.map (eqToHom h).op m)
  exact (PresheafOfModules.naturality_apply φ.val (eqToHom h).op m).symm

/-- Affine pullback monicity gives scalar-extended injectivity of the actual
section map on the original open chart. -/
theorem affineChart_pullback_tensor_injective {X : Scheme.{u}}
    (U : X.affineOpens) {M N : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ N) (T : Type u) [CommRing T] [Algebra Γ(X, U) T]
    [Mono ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) T)))).map
        ((Scheme.Modules.restrictFunctor U.property.fromSpec).map φ))] :
    Function.Injective ((show Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) from
      (φ.val.app (op U.val)).hom).baseChange T) := by
  let ψ := (Scheme.Modules.restrictFunctor U.property.fromSpec).map φ
  have hf := affinePullback_baseChange_injective Γ(X, U) T ψ
  have hc : (φ.val.app (op U.val)).hom.comp (affineChartΓIso U M).toLinearEquiv.toLinearMap =
      (affineChartΓIso U N).toLinearEquiv.toLinearMap.comp
        ((moduleSpecΓFunctor (R := Γ(X, U))).map ψ).hom := by
    ext m
    exact (congrArg (fun z ↦ z m) (affineChartΓIso_naturality U φ)).symm
  exact _root_.LinearMap.lTensor_injective_of_equiv_square
    (affineChartΓIso U M).toLinearEquiv (affineChartΓIso U N).toLinearEquiv
    ((moduleSpecΓFunctor (R := Γ(X, U))).map ψ).hom
    (φ.val.app (op U.val)).hom hc hf

end AlgebraicGeometry.Scheme.Modules
end

section
namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}}

/-- Exact compatibility of the affine pullback comparison with the original
scheme adjunction, followed by the actual tilde/global-sections adjunction. -/
@[reassoc]
theorem tildePullbackIso_homEquiv (φ : R ⟶ S) (M : ModuleCat.{u} R)
    (N : (Spec S).Modules)
    (a : tilde ((ModuleCat.extendScalars φ.hom).obj M) ⟶ N) :
    (tilde.adjunction (R := R)).homEquiv M _
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _
        ((((tildePullbackIso φ).app M)).hom ≫ a)) ≫
      (pushforwardGlobalSectionsIso φ).hom.app N =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M _
      ((tilde.adjunction (R := S)).homEquiv _ _ a) := by
  have h :
      (Adjunction.ofNatIsoRight
        ((tilde.adjunction (R := R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
        (pushforwardGlobalSectionsIso φ)).homEquiv M N
        ((((tildePullbackIso φ).app M)).hom ≫ a) =
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
        (tilde.adjunction (R := S))).homEquiv M N a := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc]
    exact congrArg
      (fun k ↦ k ≫ (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).map a)
      (Adjunction.unit_leftAdjointUniq_hom_app
        (((tilde.adjunction (R := R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
            (pushforwardGlobalSectionsIso φ))
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))) M)
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  dsimp only [Equiv.trans] at h
  exact h

@[reassoc]
theorem tildePushforwardIso_inv_homEquiv (φ : R ⟶ S) (M : ModuleCat.{u} S) :
    (tilde.adjunction (R := R)).homEquiv _ _ (((tildePushforwardIso φ).symm.app M)).hom =
      (ModuleCat.restrictScalars φ.hom).map (tilde.isoTop M).hom ≫
        (pushforwardGlobalSectionsIso φ).inv.app (tilde M) := by
  let e := ((pushforwardGlobalSectionsIso φ).app (tilde M) ≪≫
      (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop M).symm).symm
  change (tilde.adjunction (R := R)).homEquiv _ _
    ((tilde.functor R).map e.hom ≫ (tilde.adjunction (R := R)).counit.app _) = e.hom
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  change (tilde.adjunction (R := R)).unit.app _ ≫
    (tilde.functor R ⋙ moduleSpecΓFunctor).map e.hom ≫
    moduleSpecΓFunctor.map ((tilde.adjunction (R := R)).counit.app _) = e.hom
  erw [← (tilde.adjunction (R := R)).unit.naturality_assoc e.hom,
    (tilde.adjunction (R := R)).right_triangle_components, Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.Modules
end
