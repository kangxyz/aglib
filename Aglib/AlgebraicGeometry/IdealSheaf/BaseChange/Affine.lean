/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Map
public import Aglib.AlgebraicGeometry.IdealSheaf.Affine
public import Aglib.RingTheory.Flat.IdealBaseChange
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction

/-!
# Spectral comparison of the actual ideal pullback map

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FlatIdealBaseChange.lean`, SHA-256
  `52ad81197b39689c02c7f936d7b8987c9dac2695568d56796cdb1c43743a6864`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
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
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open TensorProduct
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Hom

variable {R : CommRingCat.{u}}

@[reassoc]
theorem affineStructureMap_tilde {S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.map (ModuleCat.ringHomModuleMap φ) ≫
      (((tildePushforwardIso φ).symm.app (ModuleCat.of S S))).hom =
        structureModuleMap (Spec.map φ) := by
  apply (tilde.adjunction (R := R)).homEquiv _ _ |>.injective
  erw [Adjunction.homEquiv_naturality_left, tildePushforwardIso_inv_homEquiv]
  rw [Adjunction.homEquiv_unit]
  apply (cancel_mono (affineStructurePushforwardΓIso φ).hom).mp
  change ModuleCat.ringHomModuleMap φ ≫
      (ModuleCat.restrictScalars φ.hom).map (tilde.isoTop (ModuleCat.of S S)).hom ≫
        (pushforwardGlobalSectionsIso φ).inv.app (tilde (ModuleCat.of S S)) ≫
          (affineStructurePushforwardΓIso φ).hom =
    (tilde.isoTop (ModuleCat.of R R)).hom ≫
      (moduleSpecΓFunctor (R := R)).map (structureModuleMap (Spec.map φ)) ≫
        (affineStructurePushforwardΓIso φ).hom
  rw [affineStructureMap_Γ]
  simp only [affineStructurePushforwardΓIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id]
  rfl

@[reassoc]
theorem affinePullbackTildeIso_unitToUnit {S : CommRingCat.{u}} (φ : R ⟶ S) :
    (((tildePullbackIso φ).app (ModuleCat.of R R))).hom ≫
      tilde.map (ModuleCat.scalarExtensionUnit φ) =
        SheafOfModules.pullbackObjUnitToUnit (Spec.map φ).toRingCatSheafHom := by
  apply (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ |>.injective
  have hO : (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv
      (tilde (ModuleCat.of R R)) (tilde (ModuleCat.of S S))
      (SheafOfModules.pullbackObjUnitToUnit (Spec.map φ).toRingCatSheafHom) =
      structureModuleMap (Spec.map φ) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (Spec.map φ).toRingCatSheafHom
  erw [hO]
  apply (tilde.adjunction (R := R)).homEquiv _ _ |>.injective
  apply (cancel_mono ((pushforwardGlobalSectionsIso φ).hom.app (tilde (ModuleCat.of S S)))).mp
  erw [tildePullbackIso_homEquiv]
  have htilde : (tilde.adjunction (R := S)).homEquiv _ _
      (tilde.map (ModuleCat.scalarExtensionUnit φ)) =
      ModuleCat.scalarExtensionUnit φ ≫ (tilde.isoTop (ModuleCat.of S S)).hom := by
    rw [Adjunction.homEquiv_unit]
    exact ((tilde.adjunction (R := S)).unit.naturality (ModuleCat.scalarExtensionUnit φ)).symm
  refine (congrArg ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _) htilde).trans ?_
  refine ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv_naturality_right
    (ModuleCat.scalarExtensionUnit φ) (tilde.isoTop (ModuleCat.of S S)).hom).trans ?_
  simp only [ModuleCat.scalarExtensionUnit, Equiv.apply_symm_apply]
  erw [← affineStructureMap_tilde φ, Adjunction.homEquiv_naturality_left,
    tildePushforwardIso_inv_homEquiv]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rfl

/-- On a spectral commutative square, the specified kernel/adjunction comparison
is exactly the sheafification of the scalar-extended ring-kernel map. -/
theorem affineIdealPullbackMap_eq {S R' S' : CommRingCat.{u}}
    (φ : R ⟶ S) (φ' : R' ⟶ S') (b : R ⟶ R') (a : S ⟶ S')
    (h : φ ≫ a = b ≫ φ')
    (hs : Spec.map a ≫ Spec.map φ = Spec.map φ' ≫ Spec.map b) :
    (Scheme.Modules.pullback (Spec.map b)).map (affineIdealIso φ).hom ≫
      idealPullbackMap (Spec.map φ) (Spec.map φ') (Spec.map b) (Spec.map a) hs =
    (((tildePullbackIso b).app (ModuleCat.of R (RingHom.ker φ.hom)))).hom ≫
      tilde.map (ModuleCat.extendedKernelMap φ φ' b a h) ≫ (affineIdealIso φ').hom := by
  apply (cancel_mono (idealInclusion (Spec.map φ'))).mp
  simp only [Category.assoc, idealPullbackMap_inclusion, affineIdealIso_hom_inclusion]
  rw [← Functor.map_comp_assoc, affineIdealIso_hom_inclusion]
  rw [← tilde.map_comp, ModuleCat.extendedKernelMap_inclusion, tilde.map_comp]
  rw [← affinePullbackTildeIso_unitToUnit b, ← Category.assoc]
  have hn := (tildePullbackIso b).hom.naturality
    (ModuleCat.ofHom (RingHom.ker φ.hom).subtype)
  simpa only [Functor.comp_map, Functor.comp_obj, tilde.functor_obj, tilde.functor_map,
    Iso.app_hom, Category.assoc] using
    congrArg (fun k ↦ k ≫ tilde.map (ModuleCat.scalarExtensionUnit b)) hn

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

open scoped ChangeOfRings

theorem affineIdealPullbackMap_isIso_of_scalarExtension
    {R₀ S₀ R₁ S₁ : CommRingCat.{u}} (φ : R₀ ⟶ S₀) (φ' : R₁ ⟶ S₁)
    (b : R₀ ⟶ R₁) (a : S₀ ⟶ S₁) (h : φ ≫ a = b ≫ φ')
    (hs : Spec.map a ≫ Spec.map φ = Spec.map φ' ≫ Spec.map b)
    [IsIso (ModuleCat.extendedKernelMap φ φ' b a h)] :
    IsIso (idealPullbackMap (Spec.map φ) (Spec.map φ') (Spec.map b) (Spec.map a) hs) := by
  apply (isIso_comp_left_iff
    ((Scheme.Modules.pullback (Spec.map b)).map (affineIdealIso φ).hom) _).mp
  rw [affineIdealPullbackMap_eq φ φ' b a h hs]
  have : IsIso (tilde.map (ModuleCat.extendedKernelMap φ φ' b a h)) :=
    inferInstanceAs (IsIso ((tilde.functor R₁).map (ModuleCat.extendedKernelMap φ φ' b a h)))
  infer_instance

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

open scoped ChangeOfRings
variable (R S T A : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing A]
  [Algebra R S] [Algebra R T] [Algebra R A] [Algebra S T] [IsScalarTower R S T]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem tensorQuotientSpecSquare :
    Spec.map (CommRingCat.ofHom (algebraMap T (A ⊗[R] T))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S T)) =
      Spec.map (CommRingCat.ofHom (_root_.Algebra.tensorQuotientMap R S T A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (A ⊗[R] S))) := by
  simpa only [Spec.map_comp] using congrArg Spec.map (_root_.Algebra.tensorQuotientSquare R S T A)

/-- Quotient-flat arbitrary base change on an actual spectral tensor-product square.
Only the quotient is required to be flat over the original base. -/
theorem flatQuotient_spectralIdealPullbackMap_isIso [Module.Flat R T]
    (hsurj : Function.Surjective (algebraMap S T)) :
    IsIso (idealPullbackMap
      (Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (Spec.map (CommRingCat.ofHom (_root_.Algebra.tensorQuotientMap R S T A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S (A ⊗[R] S))))
      (Spec.map (CommRingCat.ofHom (algebraMap T (A ⊗[R] T))))
      (tensorQuotientSpecSquare R S T A)) := by
  let : IsIso (ModuleCat.extendedKernelMap
      (CommRingCat.ofHom (algebraMap S T))
      (CommRingCat.ofHom (_root_.Algebra.tensorQuotientMap R S T A))
      (CommRingCat.ofHom (algebraMap S (A ⊗[R] S)))
      (CommRingCat.ofHom (algebraMap T (A ⊗[R] T)))
      (_root_.Algebra.tensorQuotientSquare R S T A)) := by
    rw [ModuleCat.spectralExtendedIdealMap_eq_quotientFlatIso R S T A hsurj]
    infer_instance
  exact affineIdealPullbackMap_isIso_of_scalarExtension _ _ _ _
    (_root_.Algebra.tensorQuotientSquare R S T A) (tensorQuotientSpecSquare R S T A)

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

open scoped ChangeOfRings

theorem flatQuotient_categorical_spectralIdealPullbackMap_isIso
    {R S T A B C : CommRingCat.{u}} (p : R ⟶ S) (i : S ⟶ T) (q : R ⟶ A)
    (b : S ⟶ B) (p' : A ⟶ B) (a : T ⟶ C) (i' : B ⟶ C)
    (H : IsPushout p q b p') (H' : IsPushout i b a i')
    (hs : Spec.map a ≫ Spec.map i = Spec.map i' ≫ Spec.map b)
    (hsurj : Function.Surjective i) (hflat : (p ≫ i).hom.Flat) :
    IsIso (idealPullbackMap (Spec.map i) (Spec.map i') (Spec.map b) (Spec.map a) hs) := by
  have := ModuleCat.flatQuotient_categorical_spectralExtendedIdealMap_isIso p i q b p' a i' H H'
    hsurj hflat
  exact affineIdealPullbackMap_isIso_of_scalarExtension i i' b a H'.w hs

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The spectral projection of a tensor-product algebra is the actual base
change of its second factor's spectral structure morphism. -/
theorem tensorSpecProjection_isPullback
    (R A K : Type u) [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (K ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K A)

end AlgebraicGeometry.Scheme
end
