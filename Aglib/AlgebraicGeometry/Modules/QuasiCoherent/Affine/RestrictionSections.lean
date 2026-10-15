/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
/-! # Actual affine open restriction sections and the original restriction unit

The comparison uses the original associated-sheaf equivalence and adjunction maps.
Quasicoherence is explicit; there is no finite-generation or noetherianity premise.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]

/-- Scalar extension of actual affine sections is the sections of the original open restriction. -/
def affineRestrictGlobalSectionsIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≅
      moduleSpecΓFunctor.obj (M.restrict (Spec.map φ)) :=
  affinePullbackGlobalSectionsIso φ M ≪≫ moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback (Spec.map φ)).symm.app M)

/-- The comparison preserves the original open-restriction adjunction unit. -/
theorem affineRestrictGlobalSectionsIso_unit
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) ≫
      (ModuleCat.restrictScalars φ.hom).map (affineRestrictGlobalSectionsIso φ M).hom =
    moduleSpecΓFunctor.map ((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app M) ≫
      (pushforwardGlobalSectionsIso φ).hom.app (M.restrict (Spec.map φ)) := by
  have h := affinePullbackGlobalSectionsIso_unit φ M
  have hn := (pushforwardGlobalSectionsIso φ).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback (Spec.map φ)).inv.app M)
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction (Spec.map φ))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)) M
  have he := congrArg (fun k => k ≫ (ModuleCat.restrictScalars φ.hom).map
    (moduleSpecΓFunctor.map
      ((Scheme.Modules.restrictFunctorIsoPullback (Spec.map φ)).inv.app M))) h
  simp only [Category.assoc] at he
  simp only [Functor.comp_map] at hn
  erw [← hn, ← Functor.map_comp_assoc, ← hu] at he
  simp only [Scheme.Modules.restrictFunctorIsoPullback, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app] at he
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at he
  simpa only [Scheme.Modules.restrictFunctorIsoPullback,
    affineRestrictGlobalSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] using he
end AlgebraicGeometry.Scheme.Modules
