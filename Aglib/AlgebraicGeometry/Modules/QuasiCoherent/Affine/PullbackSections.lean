/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction
/-! # Actual affine pullback sections and the original adjunction unit

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
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Scalar extension of actual affine sections is the sections of the original pullback. -/
def affinePullbackGlobalSectionsIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) :=
  tilde.toTildeΓNatIso.app _ ≪≫ moduleSpecΓFunctor.mapIso
    ((tildePullbackIso φ).symm.app (moduleSpecΓFunctor.obj M) ≪≫
      (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ))

/-- The comparison preserves the original scalar and geometric adjunction units. -/
theorem affinePullbackGlobalSectionsIso_unit
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) ≫
      (ModuleCat.restrictScalars φ.hom).map (affinePullbackGlobalSectionsIso φ M).hom =
    moduleSpecΓFunctor.map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
      (pushforwardGlobalSectionsIso φ).hom.app
        ((Scheme.Modules.pullback (Spec.map φ)).obj M) := by
  have h := tildePullbackIso_globalSections_unit φ (moduleSpecΓFunctor.obj M)
  have ht := (tilde.adjunction (R := R)).right_triangle_components M
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality
    M.fromTildeΓ
  have hp := (pushforwardGlobalSectionsIso φ).hom.naturality
    ((Scheme.Modules.pullback (Spec.map φ)).map M.fromTildeΓ)
  have he := congrArg (fun k => k ≫
    (ModuleCat.restrictScalars φ.hom).map
      (moduleSpecΓFunctor.map ((tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj M))) ≫
    (ModuleCat.restrictScalars φ.hom).map
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback (Spec.map φ)).map M.fromTildeΓ))) h.symm
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc] at he
  simp only [Functor.comp_map, Functor.id_map] at hn hp
  erw [← hp] at he
  erw [← Functor.map_comp_assoc, ← hn, Functor.map_comp] at he
  simp only [Functor.map_comp, ← Category.assoc] at he
  change (tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj M) ≫
    moduleSpecΓFunctor.map M.fromTildeΓ = 𝟙 _ at ht
  erw [ht, Category.id_comp] at he
  simpa only [ModuleCat.extendScalars, tilde.adjunction, affinePullbackGlobalSectionsIso,
    Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, asIso_hom, Functor.map_comp, Category.assoc] using he

end AlgebraicGeometry.Scheme.Modules
