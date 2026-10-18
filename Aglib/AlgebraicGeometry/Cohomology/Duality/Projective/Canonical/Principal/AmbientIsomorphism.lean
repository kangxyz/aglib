/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.Derived
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Affine.OpenSections
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctor

/-!
# Actual ambient affine changes in the canonical model

The original ambient restriction unit gives a scalar-extension lift on every
term of the supplied injective resolution. Its affine closed-adjoint formula
uses the original open comparison and native coinduced evaluation. In
particular, no injective-resolution term is assumed quasicoherent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open HomologicalComplex
open scoped TensorProduct ChangeOfRings

universe u w z

namespace AlgebraicGeometry.Scheme.Modules

variable {A A' B B' : CommRingCat.{u}}

private def canonicalAmbientSectionsMate (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] :
    moduleSpecΓFunctor (R := A) ⋙ ModuleCat.extendScalars φ.hom ⟶
      restrictFunctor (Spec.map φ) ⋙ moduleSpecΓFunctor (R := A') where
  app N := ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    ((affineOpenRestrictionSectionsNat φ).app N)
  naturality {M N} p := by
    dsimp only [CategoryTheory.Functor.comp_map]
    apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (affineOpenRestrictionSectionsNat φ).naturality p

private theorem canonicalAmbientSectionsMate_homEquiv (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (N : (Spec A).Modules) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
        ((canonicalAmbientSectionsMate φ).app N) =
      affineOpenRestrictionSectionsMap φ N :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).apply_symm_apply _

private theorem canonicalAmbientSectionsMate_coefficient (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (N : (Spec A).Modules) [N.IsQuasicoherent] :
    (canonicalAmbientSectionsMate φ).app N = (affineRestrictGlobalSectionsIso φ N).hom := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [canonicalAmbientSectionsMate_homEquiv, Adjunction.homEquiv_unit]
  exact (affineRestrictGlobalSectionsIso_unit φ N).symm

/-- The original affine coinduced linear map as its native module morphism. -/
def canonicalAmbientAffineHom (σ : A ⟶ B)
    [IsClosedImmersion (Spec.map σ)] (N : (Spec A).Modules)
    (m : (moduleSpecΓFunctor (R := B)).obj
      ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) :
    (ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B) ⟶
      (moduleSpecΓFunctor (R := A)).obj N :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B))
    (Y := (moduleSpecΓFunctor (R := A)).obj N)
    (closedImmersionRightAdjointSectionsLinearEquiv σ N m)

variable (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map ψ) (Spec.map τ) (Spec.map σ) (Spec.map φ))

private theorem canonicalAmbientAffineOpenHom
    (η : (ModuleCat.extendScalars φ.hom).obj
        ((ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B)) ≅
      (ModuleCat.restrictScalars τ.hom).obj (ModuleCat.of B' B'))
    (hη : ∀ b : B, η.hom
      ((1 : A') ⊗ₜ[A,φ.hom]
        (show (ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B) from b)) = ψ b)
    (N : (Spec A).Modules)
    (m : (moduleSpecΓFunctor (R := B)).obj
      ((closedImmersionRightAdjoint (Spec.map σ)).obj N)) :
    canonicalAmbientAffineHom τ ((restrictFunctor (Spec.map φ)).obj N)
        (closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N m) =
      η.inv ≫ (ModuleCat.extendScalars φ.hom).map (canonicalAmbientAffineHom σ N m) ≫
        (canonicalAmbientSectionsMate φ).app N := by
  apply (cancel_epi η.hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  have hleft : (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
      (η.hom ≫ canonicalAmbientAffineHom τ ((restrictFunctor (Spec.map φ)).obj N)
        (closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N m)) =
    canonicalAmbientAffineHom σ N m ≫ affineOpenRestrictionSectionsMap φ N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    let y : (moduleSpecΓFunctor (R := B')).obj
        ((closedImmersionRightAdjoint (Spec.map τ)).obj
          ((restrictFunctor (Spec.map φ)).obj N)) :=
      closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N m
    change closedImmersionRightAdjointSectionsLinearEquiv τ
        ((restrictFunctor (Spec.map φ)).obj N)
        y
        (η.hom ((1 : A') ⊗ₜ[A,φ.hom] b)) =
      affineOpenRestrictionSectionsMap φ N
        (closedImmersionRightAdjointSectionsLinearEquiv σ N m b)
    exact (congrArg
      (fun c : B' => closedImmersionRightAdjointSectionsLinearEquiv τ
        ((restrictFunctor (Spec.map φ)).obj N) y c) (hη b)).trans
      (closedImmersionRightAdjointAffineOpenSections_apply φ σ τ ψ h N m b)
  rw [hleft, Adjunction.homEquiv_naturality_left]
  exact congrArg (fun t => canonicalAmbientAffineHom σ N m ≫ t)
    (canonicalAmbientSectionsMate_homEquiv φ N).symm

/-- Actual affine sections of the same supplied resolution restricted to the ambient open. -/
def canonicalAmbientLocalΓResolution
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L) :
    InjectiveResolution ((moduleSpecΓFunctor (R := A')).obj
      ((restrictFunctor (Spec.map φ)).obj L)) := by
  letI : ((restrictFunctor (Spec.map φ)).obj L).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec A').ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback (Spec.map φ)).symm.app L) (isQuasicoherent_pullback φ L)
  exact AffineDerived.globalSectionsInjectiveResolution
    (affineOpenRestrictedInjectiveResolution φ J)

private def canonicalAmbientSectionResolutionLift
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L) :
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (.up ℕ)).obj
        (AffineDerived.globalSectionsInjectiveResolution J).cocomplex ⟶
      (canonicalAmbientLocalΓResolution φ J).cocomplex where
  f n := (canonicalAmbientSectionsMate φ).app (J.cocomplex.X n)
  comm' n m _ := by
    change (canonicalAmbientSectionsMate φ).app (J.cocomplex.X n) ≫
        moduleSpecΓFunctor.map ((restrictFunctor (Spec.map φ)).map (J.cocomplex.d n m)) =
      (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map (J.cocomplex.d n m)) ≫
        (canonicalAmbientSectionsMate φ).app (J.cocomplex.X m)
    exact ((canonicalAmbientSectionsMate φ).naturality (J.cocomplex.d n m)).symm

private theorem canonicalAmbientSectionResolutionLift_augmentation
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L) :
    (ModuleCat.extendScalars φ.hom).map
        ((AffineDerived.globalSectionsInjectiveResolution J).ι.f 0) ≫
      (canonicalAmbientSectionResolutionLift φ J).f 0 =
    (canonicalAmbientSectionsMate φ).app L ≫
      (canonicalAmbientLocalΓResolution φ J).ι.f 0 := by
  change (ModuleCat.extendScalars φ.hom).map
      ((AffineDerived.globalSectionsAugmentation J).f 0) ≫
      (canonicalAmbientSectionsMate φ).app (J.cocomplex.X 0) =
    (canonicalAmbientSectionsMate φ).app L ≫
      (AffineDerived.globalSectionsAugmentation (affineOpenRestrictedInjectiveResolution φ J)).f 0
  rw [AffineDerived.globalSectionsAugmentation_f_zero,
    AffineDerived.globalSectionsAugmentation_f_zero]
  change (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map (J.ι.f 0)) ≫
      (canonicalAmbientSectionsMate φ).app (J.cocomplex.X 0) =
    (canonicalAmbientSectionsMate φ).app L ≫
      moduleSpecΓFunctor.map ((J.mapAugmentation (restrictFunctor (Spec.map φ))).f 0)
  rw [InjectiveResolution.mapAugmentation_f_zero]
  exact (canonicalAmbientSectionsMate φ).naturality (J.ι.f 0)

variable
  (η : (ModuleCat.extendScalars φ.hom).obj
      ((ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B)) ≅
    (ModuleCat.restrictScalars τ.hom).obj (ModuleCat.of B' B'))
  (hη : ∀ b : B, η.hom
    ((1 : A') ⊗ₜ[A,φ.hom]
      (show (ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B) from b)) = ψ b)
  {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

include η hη in
/-- The actual geometric affine open-square map carries each original resolution
cocycle to a cocycle in the same restricted resolution. -/
theorem canonicalAmbientAffineOpenHom_cycle (n : ℕ)
    (m : (moduleSpecΓFunctor (R := B)).obj
      ((closedImmersionRightAdjoint (Spec.map σ)).obj (J.cocomplex.X n)))
    (hf : canonicalAmbientAffineHom σ (J.cocomplex.X n) m ≫
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0) :
    canonicalAmbientAffineHom τ ((restrictFunctor (Spec.map φ)).obj (J.cocomplex.X n))
        (closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h (J.cocomplex.X n) m) ≫
      (canonicalAmbientLocalΓResolution φ J).cocomplex.d n (n + 1) = 0 := by
  have hc := CategoryTheory.InjectiveResolution.ExactFunctor.mappedCycle_comp_d
    (F := ModuleCat.extendScalars φ.hom)
    (R := AffineDerived.globalSectionsInjectiveResolution J)
    (S := canonicalAmbientLocalΓResolution φ J)
    (canonicalAmbientSectionResolutionLift φ J) n
    (canonicalAmbientAffineHom σ (J.cocomplex.X n) m) hf
  rw [canonicalAmbientAffineOpenHom φ σ τ ψ h η hη]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom hc (η.inv x)

include hη in
/-- The literal geometric open-square map on a cocycle gives the original exact
scalar-extension Ext map, with the supplied original source isomorphism and
the original coefficient restriction isomorphism. Its source normalization
is the explicit unit-tensor equation, not an assumed Ext-naturality family. -/
theorem canonicalAmbientAffineOpenExtMk
    (hφ : φ.hom.Flat) [HasExt.{w} (ModuleCat.{u} A)]
    [HasExt.{z} (ModuleCat.{u} A')] (n : ℕ)
    (m : (moduleSpecΓFunctor (R := B)).obj
      ((closedImmersionRightAdjoint (Spec.map σ)).obj (J.cocomplex.X n)))
    (hf : canonicalAmbientAffineHom σ (J.cocomplex.X n) m ≫
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0) :
    let F : ModuleCat.{u} A ⥤ ModuleCat.{u} A' := ModuleCat.extendScalars φ.hom
    letI : PreservesFiniteLimits F := ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hφ
    letI : PreservesFiniteColimits F :=
      ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ hφ
    ((Ext.mk₀ η.inv).comp
      (((AffineDerived.globalSectionsInjectiveResolution J).extMk
        (canonicalAmbientAffineHom σ (J.cocomplex.X n) m) (n + 1) rfl hf :
          Ext.{w} ((ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B))
            (moduleSpecΓFunctor.obj L) n).mapExactFunctor F) (Nat.zero_add n)).comp
      (Ext.mk₀ (affineRestrictGlobalSectionsIso φ L).hom) (Nat.add_zero n) =
    ((canonicalAmbientLocalΓResolution φ J).extMk
      (canonicalAmbientAffineHom τ ((restrictFunctor (Spec.map φ)).obj (J.cocomplex.X n))
        (closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h (J.cocomplex.X n) m))
      (n + 1) rfl (canonicalAmbientAffineOpenHom_cycle φ σ τ ψ h η hη J n m hf) :
        Ext.{z} ((ModuleCat.restrictScalars τ.hom).obj (ModuleCat.of B' B'))
          ((moduleSpecΓFunctor (R := A')).obj ((restrictFunctor (Spec.map φ)).obj L)) n) := by
  let F : ModuleCat.{u} A ⥤ ModuleCat.{u} A' := ModuleCat.extendScalars φ.hom
  let : PreservesFiniteLimits F :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hφ
  let : PreservesFiniteColimits F :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ hφ
  let β : Ext.{z} ((ModuleCat.restrictScalars τ.hom).obj (ModuleCat.of B' B'))
      (F.obj ((moduleSpecΓFunctor (R := A)).obj L)) n :=
    (Ext.mk₀ η.inv).comp
      (((AffineDerived.globalSectionsInjectiveResolution J).extMk
        (canonicalAmbientAffineHom σ (J.cocomplex.X n) m) (n + 1) rfl hf :
          Ext.{w} ((ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B))
            (moduleSpecΓFunctor.obj L) n).mapExactFunctor F) (Nat.zero_add n)
  have hmap : β.comp (Ext.mk₀ ((canonicalAmbientSectionsMate φ).app L)) (Nat.add_zero n) = _ :=
    CategoryTheory.InjectiveResolution.ExactFunctor.mk₀_comp_extMk_mapExactFunctor_comp_mk₀
      F (AffineDerived.globalSectionsInjectiveResolution J)
      (canonicalAmbientLocalΓResolution φ J) ((canonicalAmbientSectionsMate φ).app L)
      (canonicalAmbientSectionResolutionLift φ J)
      (canonicalAmbientSectionResolutionLift_augmentation φ J)
      (canonicalAmbientAffineHom σ (J.cocomplex.X n) m) hf η.inv
  have he := canonicalAmbientAffineOpenHom φ σ τ ψ h η hη (J.cocomplex.X n) m
  change _ = η.inv ≫ F.map (canonicalAmbientAffineHom σ (J.cocomplex.X n) m) ≫
    (canonicalAmbientSectionResolutionLift φ J).f n at he
  have hcoefficient : β.comp (Ext.mk₀ (affineRestrictGlobalSectionsIso φ L).hom)
      (Nat.add_zero n) =
      β.comp (Ext.mk₀ ((canonicalAmbientSectionsMate φ).app L)) (Nat.add_zero n) :=
    congrArg
      (fun f : F.obj ((moduleSpecΓFunctor (R := A)).obj L) ⟶
          (moduleSpecΓFunctor (R := A')).obj ((restrictFunctor (Spec.map φ)).obj L) =>
        β.comp (Ext.mk₀ f) (Nat.add_zero n))
      (canonicalAmbientSectionsMate_coefficient φ L).symm
  refine hcoefficient.trans (hmap.trans ?_)
  congr 1
  exact he.symm

end AlgebraicGeometry.Scheme.Modules
