/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.AffineChartRestrictionMap

/-! # The original affine-chart restriction as a pullback coefficient arrow -/

@[expose] public noncomputable section

open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original inverse restriction/pullback comparison preserves the original
adjunction unit. No quasicoherence or target hypothesis is used. -/
theorem restrictFunctorIsoPullback_inv_unit_app {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    (pullbackPushforwardAdjunction f).unit.app M ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).inv.app M) =
      (restrictAdjunction f).unit.app M := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (restrictAdjunction f) (pullbackPushforwardAdjunction f) M
  change (restrictAdjunction f).unit.app M ≫
    (pushforward f).map ((restrictFunctorIsoPullback f).hom.app M) =
      (pullbackPushforwardAdjunction f).unit.app M at h
  have hcancel :
      (pushforward f).map ((restrictFunctorIsoPullback f).hom.app M) ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).inv.app M) =
      𝟙 ((pushforward f).obj ((restrictFunctor f).obj M)) :=
    ((pushforward f).map_comp
      ((restrictFunctorIsoPullback f).hom.app M)
      ((restrictFunctorIsoPullback f).inv.app M)).symm.trans
        ((congrArg (fun k => (pushforward f).map k)
          (Iso.hom_inv_id_app (restrictFunctorIsoPullback f) M)).trans
            ((pushforward f).map_id ((restrictFunctor f).obj M)))
  calc
    _ = ((restrictAdjunction f).unit.app M ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).hom.app M)) ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).inv.app M) :=
      congrArg (fun k => k ≫
        (pushforward f).map ((restrictFunctorIsoPullback f).inv.app M)) h.symm
    _ = (restrictAdjunction f).unit.app M ≫
        ((pushforward f).map ((restrictFunctorIsoPullback f).hom.app M) ≫
          (pushforward f).map ((restrictFunctorIsoPullback f).inv.app M)) :=
      Category.assoc _ _ _
    _ = (restrictAdjunction f).unit.app M ≫
        𝟙 ((pushforward f).obj ((restrictFunctor f).obj M)) :=
      congrArg (fun k => (restrictAdjunction f).unit.app M ≫ k) hcancel
    _ = (restrictAdjunction f).unit.app M := Category.comp_id _

/-- The scalar-adjoint coefficient arrow of the original chart pullback
comparison is precisely the original affine restriction linear map. -/
theorem affineChartRestrictionLinearMap_pullback {X : Scheme.{u}} {R D : CommRingCat.{u}}
    (φ : R ⟶ D) (j : Spec R ⟶ X) (j' : Spec D ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ j = j') (M : X.Modules) :
    letI := φ.hom.toAlgebra
    letI : SMul R D := Algebra.toSMul
    (moduleSpecΓFunctor.map
        ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (M.restrict j) ≫
          (pushforward (Spec.map φ)).map
            ((restrictFunctorIsoPullback (Spec.map φ)).inv.app (M.restrict j) ≫
              (affineChartRestrictionIso φ j j' hc M).hom)) ≫
        (pushforwardGlobalSectionsIso φ).hom.app (M.restrict j')).hom =
      affineChartRestrictionLinearMap φ j j' hc M := by
  let := φ.hom.toAlgebra
  let : SMul R D := Algebra.toSMul
  have hu :
      (pullbackPushforwardAdjunction (Spec.map φ)).unit.app (M.restrict j) ≫
          (pushforward (Spec.map φ)).map
            ((restrictFunctorIsoPullback (Spec.map φ)).inv.app (M.restrict j) ≫
              (affineChartRestrictionIso φ j j' hc M).hom) =
        (restrictAdjunction (Spec.map φ)).unit.app (M.restrict j) ≫
          (pushforward (Spec.map φ)).map (affineChartRestrictionIso φ j j' hc M).hom := by
    rw [Functor.map_comp, ← Category.assoc, restrictFunctorIsoPullback_inv_unit_app]
  rw [hu, Functor.map_comp, Category.assoc]
  have hn := (pushforwardGlobalSectionsIso φ).hom.naturality
    (affineChartRestrictionIso φ j j' hc M).hom
  change moduleSpecΓFunctor.map
        ((pushforward (Spec.map φ)).map (affineChartRestrictionIso φ j j' hc M).hom) ≫
      (pushforwardGlobalSectionsIso φ).hom.app (M.restrict j') =
    (pushforwardGlobalSectionsIso φ).hom.app ((M.restrict j).restrict (Spec.map φ)) ≫
      (ModuleCat.restrictScalars φ.hom).map
        (moduleSpecΓFunctor.map (affineChartRestrictionIso φ j j' hc M).hom) at hn
  rw [hn]
  rfl

end AlgebraicGeometry.Scheme.Modules
