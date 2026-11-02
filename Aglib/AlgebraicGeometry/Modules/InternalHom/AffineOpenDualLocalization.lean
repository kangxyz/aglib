/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineEvaluation
public import Aglib.AlgebraicGeometry.Modules.InternalHom.BidualAffine
public import Aglib.AlgebraicGeometry.Modules.Locality.AffineChartRestrictionMap
public import Aglib.RingTheory.Localization.HomFinitePresentation

/-!
# Original dual coordinates on actual affine opens

Actual Hom evaluation commutes with restriction. Native localization uniqueness
therefore identifies the dual restriction. The chart comparisons below retain
the original affine dual and bidual coordinates, not replacement sheaf models.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

variable {X : Scheme.{u}}

local instance affineOpenDualFromSpec_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion U.property.fromSpec :=
  IsAffineOpen.isOpenImmersion_fromSpec U.property

/-- On an actual affine open the original unit coordinate is the original
scalar-compatible chart comparison. -/
theorem affineRestrictionUnitSectionsEquiv_affineOpen (U : X.affineOpens)
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).restrict
        U.property.fromSpec)) :
    affineRestrictionUnitSectionsEquiv U.property.fromSpec s =
      (affineChartΓIso U (SheafOfModules.unit X.ringCatSheaf)).hom s := by
  let k : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) :=
    (affineChartΓIso U (SheafOfModules.unit X.ringCatSheaf)).hom.hom.comp
      (affineRestrictionUnitSectionsEquiv U.property.fromSpec).symm.toLinearMap
  have hk1 : k 1 = 1 := by
    let h : U.val = U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := by
      simp [Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec]
    have hmap : (affineChartΓIso U (SheafOfModules.unit X.ringCatSheaf)).hom
        (1 : Γ(X, U.property.fromSpec ''ᵁ ⊤)) = (1 : Γ(X, U)) := by
      change (X.presheaf.map (eqToHom h).op) 1 = 1
      exact (X.presheaf.map (eqToHom h).op).hom.map_one
    exact (congrArg (affineChartΓIso U (SheafOfModules.unit X.ringCatSheaf)).hom
      (affineChartUnitSections_symm_one U.property.fromSpec)).trans hmap
  have hk : k = LinearMap.id := by
    apply LinearMap.ext_ring
    exact hk1
  obtain ⟨r, rfl⟩ := (affineRestrictionUnitSectionsEquiv U.property.fromSpec).symm.surjective s
  exact ((affineRestrictionUnitSectionsEquiv U.property.fromSpec).apply_symm_apply r).trans
    (LinearMap.congr_fun hk r).symm

/-- The named affine dual coordinate is evaluation on the same actual affine
open after the original Gamma chart comparisons. -/
theorem affineDualSectionsEquiv_affineOpen_apply (U : X.affineOpens) (M : X.Modules)
    [(M.restrict U.property.fromSpec).IsQuasicoherent]
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X M).restrict U.property.fromSpec))
    (m : moduleSpecΓFunctor.obj (M.restrict U.property.fromSpec)) :
    affineDualSectionsEquiv U.property.fromSpec M s m =
      affineSectionsEquiv U M (SheafOfModules.unit X.ringCatSheaf)
        ((affineChartΓIso U (dualSheaf X M)).hom s) ((affineChartΓIso U M).hom m) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let z : moduleSpecΓFunctor.obj (O.restrict U.property.fromSpec) :=
    s.val.app (op (Over.mk (𝟙 (U.property.fromSpec ''ᵁ ⊤)))) m
  have hdual : affineDualSectionsEquiv U.property.fromSpec M s m =
      affineRestrictionUnitSectionsEquiv U.property.fromSpec z :=
    affineDualSectionsEquiv_apply U.property.fromSpec M s m
  have hunit : affineRestrictionUnitSectionsEquiv U.property.fromSpec z =
      (affineChartΓIso U O).hom z :=
    affineRestrictionUnitSectionsEquiv_affineOpen U z
  let h : U.val = U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := by
    simp [Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec]
  exact hdual.trans (hunit.trans
    (sectionEvaluation_restrict X M O (eqToHom h) s m).symm)

/-- Transporting a raw coordinate through the original Gamma comparison also
transports its original named dual coordinate. -/
theorem affineDualCoordinate_affineOpen (U : X.affineOpens) (M : X.Modules)
    [(M.restrict U.property.fromSpec).IsQuasicoherent]
    {P : Type*} [AddCommMonoid P] [Module Γ(X, U) P]
    (e : moduleSpecΓFunctor.obj (M.restrict U.property.fromSpec) ≃ₗ[Γ(X, U)] P)
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X M).restrict U.property.fromSpec)) :
    ((affineDualSectionsEquiv U.property.fromSpec M).trans e.symm.dualMap) s =
      ((affineSectionsEquiv U M (SheafOfModules.unit X.ringCatSheaf)).trans
        ((affineChartΓIso U M).toLinearEquiv.symm.trans e).symm.dualMap)
          ((affineChartΓIso U (dualSheaf X M)).hom s) := by
  apply LinearMap.ext
  intro x
  exact affineDualSectionsEquiv_affineOpen_apply U M s (e.symm x)

/-- The two named dual coordinates give the same original bidual coordinate
as actual-open evaluation twice. This is a coordinate comparison, not an
assumption about restriction of the bidual. -/
theorem affineBidualCoordinate_affineOpen (U : X.affineOpens) (M : X.Modules)
    [(M.restrict U.property.fromSpec).IsQuasicoherent]
    [((show X.Modules from dualSheaf X M).restrict U.property.fromSpec).IsQuasicoherent]
    {P : Type*} [AddCommMonoid P] [Module Γ(X, U) P]
    (e : moduleSpecΓFunctor.obj (M.restrict U.property.fromSpec) ≃ₗ[Γ(X, U)] P)
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict U.property.fromSpec)) :
    letI : Module Γ(X, U) Γ(dualSheaf X M, U) :=
      ((dualSheaf X M).val.obj (op U.val)).isModule
    let d := (affineDualSectionsEquiv U.property.fromSpec M).trans e.symm.dualMap
    let dO : Γ(dualSheaf X M, U) ≃ₗ[Γ(X, U)]
        Module.Dual Γ(X, U) P :=
      (affineSectionsEquiv U M (SheafOfModules.unit X.ringCatSheaf)).trans
        ((affineChartΓIso U M).toLinearEquiv.symm.trans e).symm.dualMap
    ((affineDualSectionsEquiv U.property.fromSpec (dualSheaf X M)).trans
      d.symm.dualMap) s =
      ((affineSectionsEquiv U (dualSheaf X M)
        (SheafOfModules.unit X.ringCatSheaf)).trans dO.symm.dualMap)
          ((affineChartΓIso U (dualSheaf X (dualSheaf X M))).hom s) := by
  let : Module Γ(X, U) Γ(dualSheaf X M, U) :=
    ((dualSheaf X M).val.obj (op U.val)).isModule
  intro d dO
  apply LinearMap.ext
  intro ell
  have hi : (affineChartΓIso U (dualSheaf X M)).hom (d.symm ell) = dO.invFun ell := by
    exact dO.injective
      ((affineDualCoordinate_affineOpen U M e (d.symm ell)).symm.trans
        ((d.apply_symm_apply ell).trans (dO.apply_symm_apply ell).symm))
  change affineDualSectionsEquiv U.property.fromSpec (dualSheaf X M) s (d.symm ell) = _
  exact (affineDualSectionsEquiv_affineOpen_apply U (dualSheaf X M) s
    (d.symm ell)).trans (congrArg
      (affineSectionsEquiv U (dualSheaf X M) (SheafOfModules.unit X.ringCatSheaf)
        ((affineChartΓIso U (dualSheaf X (dualSheaf X M))).hom s)) hi)

/-- The original actual-open dual restriction is native Hom localization.
The sole coordinate input is restriction of the source module, independently
of any dual or bidual restriction law. -/
theorem affineDualCoordinate_restrict (U V : X.affineOpens) (i : V.val ⟶ U.val)
    (M : X.Modules)
    [(M.restrict U.property.fromSpec).IsQuasicoherent]
    [(M.restrict V.property.fromSpec).IsQuasicoherent]
    (S : Submonoid Γ(X, U)) :
    letI := (X.presheaf.map i.op).hom.toAlgebra
    letI : SMul Γ(X, U) Γ(X, V) := Algebra.toSMul
    ∀ [_localization : IsLocalization S Γ(X, V)],
    ∀ {P Q : Type*} [AddCommMonoid P] [Module Γ(X, U) P]
    [AddCommMonoid Q] [Module Γ(X, U) Q] [Module Γ(X, V) Q]
    [_towerQ : IsScalarTower Γ(X, U) Γ(X, V) Q]
    (e : Γ(M, U) ≃ₗ[Γ(X, U)] P) (e' : Γ(M, V) ≃ₗ[Γ(X, V)] Q)
    (q : P →ₗ[Γ(X, U)] Q) [_localizedQ : IsLocalizedModule S q]
    (_hq : ∀ m, e' (M.val.map i.op m) = q (e m))
    (s : Γ(dualSheaf X M, U)),
    ((affineSectionsEquiv V M (SheafOfModules.unit X.ringCatSheaf)).trans
      e'.symm.dualMap) ((dualSheaf X M).val.map i.op s) =
      IsLocalizedModule.mapExtendScalars S q (Algebra.linearMap Γ(X, U) Γ(X, V))
        Γ(X, V) (((affineSectionsEquiv U M
          (SheafOfModules.unit X.ringCatSheaf)).trans e.symm.dualMap) s) := by
  let := (X.presheaf.map i.op).hom.toAlgebra
  let : SMul Γ(X, U) Γ(X, V) := Algebra.toSMul
  dsimp only
  intro _ P Q _ _ _ _ _ _ e e' q _ hq s
  apply LinearMap.restrictScalars_injective Γ(X, U)
  apply IsLocalizedModule.linearMap_ext S q (Algebra.linearMap Γ(X, U) Γ(X, V))
  ext x
  have hx : q x = e' (M.val.map i.op (e.symm x)) := by
    simpa only [LinearEquiv.apply_symm_apply] using (hq (e.symm x)).symm
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
  change affineSectionsEquiv V M (SheafOfModules.unit X.ringCatSheaf)
      ((dualSheaf X M).val.map i.op s) (e'.symm (q x)) =
    algebraMap Γ(X, U) Γ(X, V)
      (affineSectionsEquiv U M (SheafOfModules.unit X.ringCatSheaf) s (e.symm x))
  have harg : e'.symm (q x) = M.val.map i.op (e.symm x) :=
    (congrArg e'.symm hx).trans (e'.symm_apply_apply _)
  exact (congrArg
    (affineSectionsEquiv V M (SheafOfModules.unit X.ringCatSheaf)
      ((dualSheaf X M).val.map i.op s)) harg).trans
        (affineSectionsEquiv_restrict U V M (SheafOfModules.unit X.ringCatSheaf)
          i s (e.symm x))

end AlgebraicGeometry.Scheme.Modules.InternalHom
