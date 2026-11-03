/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.AffineChartRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom.BidualAffine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.OpenRestrictionSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PrincipalSections

/-!
# Original linear restriction between affine charts
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped ModuleCat.Algebra

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {Λ R D : CommRingCat.{u}}

/-- The original restriction-unit map in the original affine chart coordinates. -/
def affineChartRestrictionLinearMap (φ : R ⟶ D) (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ j = j') (M : X.Modules) :
    letI := φ.hom.toAlgebra
    letI : SMul R D := Algebra.toSMul
    moduleSpecΓFunctor.obj (M.restrict j) →ₗ[R]
      moduleSpecΓFunctor.obj (M.restrict j') := by
  let := φ.hom.toAlgebra
  let : SMul R D := Algebra.toSMul
  exact ((moduleSpecΓFunctor.map
    (affineChartRestrictionIso φ j j' hc M).hom).hom.restrictScalars R).comp
      (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app (M.restrict j)) ≫
        (pushforwardGlobalSectionsIso φ).hom.app ((M.restrict j).restrict (Spec.map φ))).hom

theorem affineChartRestrictionLinearMap_comp_function
    (φ : R ⟶ D) (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ j = j') (M : X.Modules) {P : Type*}
    (e : moduleSpecΓFunctor.obj (M.restrict j') → P) :
    letI := φ.hom.toAlgebra
    letI : SMul R D := Algebra.toSMul
    (fun s : moduleSpecΓFunctor.obj (M.restrict j) =>
      e ((((moduleSpecΓFunctor.map
        (affineChartRestrictionIso φ j j' hc M).hom).hom.restrictScalars R).comp
          (moduleSpecΓFunctor.map
            ((restrictAdjunction (Spec.map φ)).unit.app (M.restrict j)) ≫
              (pushforwardGlobalSectionsIso φ).hom.app
                ((M.restrict j).restrict (Spec.map φ))).hom) s)) =
      (fun s => e (affineChartRestrictionLinearMap φ j j' hc M s)) := rfl

/-- The original chart restriction is the actual presheaf restriction. -/
theorem affineChartRestrictionLinearMap_apply (φ : R ⟶ D) (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ j = j')
    (M : X.Modules) (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    affineChartRestrictionLinearMap φ j j' hc M m =
      M.presheaf.map (homOfLE (affineChart_image_le φ j j' hc)).op m :=
  affineChartRestrictionIso_unit φ j j' hc M m

/-- Original inverse unit coordinates are native structure-sheaf transport. -/
theorem affineChartUnitSections_symm_apply (j : Spec R ⟶ X) [IsOpenImmersion j] (r : R) :
    (affineRestrictionUnitSectionsEquiv j).symm r =
      (j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r) := rfl

/-- Original inverse unit coordinates preserve one. -/
theorem affineChartUnitSections_symm_one (j : Spec R ⟶ X) [IsOpenImmersion j] :
    (affineRestrictionUnitSectionsEquiv j).symm 1 = (1 : Γ(X, j ''ᵁ ⊤)) := by
  exact (affineChartUnitSections_symm_apply j 1).trans
    ((congrArg (j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv.hom.map_one)).trans
      (j.appIso ⊤).inv.hom.map_one)

/-- The actual unit restriction preserves the original coordinate-ring map. -/
theorem affineChartUnitSections_restriction (φ : R ⟶ D) (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ j = j')
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).restrict j)) :
    letI := φ.hom.toAlgebra
    letI : SMul R D := Algebra.toSMul
    affineRestrictionUnitSectionsEquiv j'
      (affineChartRestrictionLinearMap φ j j' hc (SheafOfModules.unit X.ringCatSheaf) s) =
    algebraMap R D (affineRestrictionUnitSectionsEquiv j s) := by
  let := φ.hom.toAlgebra
  let : SMul R D := Algebra.toSMul
  obtain ⟨r, rfl⟩ := (affineRestrictionUnitSectionsEquiv j).symm.surjective s
  let g : R →ₗ[R] D :=
    ((affineRestrictionUnitSectionsEquiv j').toLinearMap.restrictScalars R).comp
      ((affineChartRestrictionLinearMap φ j j' hc (SheafOfModules.unit X.ringCatSheaf)).comp
        (affineRestrictionUnitSectionsEquiv j).symm.toLinearMap)
  have hres : affineChartRestrictionLinearMap φ j j' hc (SheafOfModules.unit X.ringCatSheaf)
      ((affineRestrictionUnitSectionsEquiv j).symm 1) =
      (affineRestrictionUnitSectionsEquiv j').symm 1 := by
    have hres1 : affineChartRestrictionLinearMap φ j j' hc (SheafOfModules.unit X.ringCatSheaf)
        (1 : Γ(X, j ''ᵁ ⊤)) = (1 : Γ(X, j' ''ᵁ ⊤)) :=
      (affineChartRestrictionLinearMap_apply φ j j' hc (SheafOfModules.unit X.ringCatSheaf) _).trans
        ((X.presheaf.map (homOfLE (affineChart_image_le φ j j' hc)).op).hom.map_one)
    exact (congrArg (affineChartRestrictionLinearMap φ j j' hc (SheafOfModules.unit X.ringCatSheaf))
      (affineChartUnitSections_symm_one j)).trans
        (hres1.trans (affineChartUnitSections_symm_one j').symm)
  have h1 : g 1 = 1 :=
    (congrArg (affineRestrictionUnitSectionsEquiv j') hres).trans
      ((affineRestrictionUnitSectionsEquiv j').apply_symm_apply 1)
  change g r = algebraMap R D _
  rw [LinearEquiv.apply_symm_apply]
  have hg : g = Algebra.linearMap R D := by
    apply LinearMap.ext_ring
    simpa only [Algebra.linearMap_apply, map_one] using h1
  exact LinearMap.congr_fun hg r

theorem affineChartRestrictionLinearMap_principal_apply
    (j : Spec R ⟶ X) [IsOpenImmersion j] (t : R)
    (M : X.Modules) (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    affineChartRestrictionLinearMap (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
      j (principalOpen R t ≫ j) rfl M m =
      (((moduleSpecΓFunctor.map
        ((restrictFunctorComp (principalOpen R t) j).inv.app M)).hom.restrictScalars R).comp
          (toPrincipalGlobalSections R t (M.restrict j))) m := by
  rw [affineChartRestrictionLinearMap_apply]
  let f : (j ''ᵁ (principalOpen R t ''ᵁ ⊤)) ⟶ (j ''ᵁ ⊤) :=
    homOfLE (j.image_mono le_top)
  let g : ((principalOpen R t ≫ j) ''ᵁ ⊤) ⟶
      (j ''ᵁ (principalOpen R t ''ᵁ ⊤)) :=
    eqToHom (Scheme.Hom.comp_image (principalOpen R t) j ⊤)
  change _ = M.presheaf.map g.op (M.presheaf.map f.op m)
  exact ((ConcreteCategory.congr_hom (M.presheaf.map_comp f.op g.op).symm m).trans
    (ConcreteCategory.congr_hom
      (congrArg M.presheaf.map (Subsingleton.elim (f.op ≫ g.op)
        (homOfLE (affineChart_image_le
          (CommRingCat.ofHom (algebraMap R (Localization.Away t))) j
          (principalOpen R t ≫ j) rfl)).op)) m)).symm

theorem affineOpenRestriction_isOpenImmersion
    (U V : X.affineOpens) (i : V.val ⟶ U.val) :
    IsOpenImmersion (Spec.map (X.presheaf.map i.op)) := by
  let : IsOpenImmersion U.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.property
  let : IsOpenImmersion V.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec V.property
  have hc := U.property.map_fromSpec V.property i.op
  have : IsOpenImmersion (Spec.map (X.presheaf.map i.op) ≫ U.property.fromSpec) := by
    rw [hc]
    infer_instance
  exact IsOpenImmersion.of_comp _ U.property.fromSpec

theorem affineChartRestrictionLinearMap_affineOpens
    (U V : X.affineOpens) (i : V.val ⟶ U.val)
    [IsOpenImmersion (Spec.map (X.presheaf.map i.op))]
    (M : X.Modules) (m : Γ(M, U)) :
    letI : IsOpenImmersion U.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.property
    letI : IsOpenImmersion V.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec V.property
    affineChartRestrictionLinearMap (X.presheaf.map i.op) U.property.fromSpec V.property.fromSpec
      (U.property.map_fromSpec V.property i.op) M ((affineChartΓIso U M).inv m) =
      (affineChartΓIso V M).inv (M.val.map i.op m) := by
  let : IsOpenImmersion U.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.property
  let : IsOpenImmersion V.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec V.property
  apply (affineChartΓIso V M).toLinearEquiv.injective
  have h := affineChartRestrictionSectionsIso_unit U V i M ((affineChartΓIso U M).inv m)
  change (affineChartΓIso V M).hom
      (affineChartRestrictionLinearMap (X.presheaf.map i.op) U.property.fromSpec V.property.fromSpec
        (U.property.map_fromSpec V.property i.op) M ((affineChartΓIso U M).inv m)) =
      M.val.map i.op ((affineChartΓIso U M).hom ((affineChartΓIso U M).inv m)) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h.trans ((affineChartΓIso V M).inv_hom_id_apply _).symm


end AlgebraicGeometry.Scheme.Modules
