/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionGeneration

/-!
# Scalar extension along original affine-open restrictions

The actual section module on a smaller affine open is extension of scalars
of the actual section module on the larger affine open. The unit equation
is the original presheaf restriction, including both affine chart comparisons.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U V : X.affineOpens) (i : V.val ⟶ U.val)
  (M : X.Modules)

private theorem affineOpenRestriction_isOpenImmersion :
    IsOpenImmersion (Spec.map (X.presheaf.map i.op)) := by
  have hc := U.property.map_fromSpec V.property i.op
  have : IsOpenImmersion (Spec.map (X.presheaf.map i.op) ≫ U.property.fromSpec) :=
    hc ▸ inferInstance
  exact IsOpenImmersion.of_comp _ U.property.fromSpec

local instance : IsOpenImmersion (Spec.map (X.presheaf.map i.op)) :=
  affineOpenRestriction_isOpenImmersion U V i

/-- The canonical spectrum-chart comparison on the smaller original open. -/
def affineChartRestrictionSectionsIso :
    moduleSpecΓFunctor.obj
      ((M.restrict U.property.fromSpec).restrict (Spec.map (X.presheaf.map i.op))) ≅
      ModuleCat.of Γ(X, V) Γ(M, V) :=
  moduleSpecΓFunctor.mapIso
    (((restrictFunctorComp (Spec.map (X.presheaf.map i.op)) U.property.fromSpec).symm.app M) ≪≫
      (restrictFunctorCongr (U.property.map_fromSpec V.property i.op)).app M) ≪≫
    affineChartΓIso V M

/-- The spectrum-chart comparison sends the native restriction unit to the
original module-presheaf restriction. -/
theorem affineChartRestrictionSectionsIso_unit
    (m : moduleSpecΓFunctor.obj (M.restrict U.property.fromSpec)) :
    (affineChartRestrictionSectionsIso U V i M).hom
      ((((restrictAdjunction (Spec.map (X.presheaf.map i.op))).unit.app
        (M.restrict U.property.fromSpec)).app ⊤) m) =
      M.val.map i.op ((affineChartΓIso U M).hom m) := by
  change Γ(M, U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) at m
  change (affineChartΓIso V M).hom
    ((((restrictFunctorCongr (U.property.map_fromSpec V.property i.op)).hom.app M).app ⊤)
      ((((restrictFunctorComp (Spec.map (X.presheaf.map i.op))
        U.property.fromSpec).inv.app M).app ⊤)
        ((((restrictAdjunction (Spec.map (X.presheaf.map i.op))).unit.app
          (M.restrict U.property.fromSpec)).app ⊤) m))) = _
  rw [restrictFunctorCongr_hom_app_app, restrictFunctorComp_inv_app_app,
    restrictAdjunction_unit_app_app, restrict_map]
  have hchart (W : X.affineOpens)
      (x : moduleSpecΓFunctor.obj (M.restrict W.property.fromSpec)) :
      (affineChartΓIso W M).hom x = M.presheaf.map
        (eqToHom (show W.val = W.property.fromSpec ''ᵁ ⊤ from by
          simp [Scheme.Hom.image_top_eq_opensRange,
            W.property.opensRange_fromSpec])).op x := rfl
  rw [hchart, hchart]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _
    (M.presheaf.map _ m))) = M.presheaf.map i.op (M.presheaf.map _ m)
  simp only [← Functor.map_comp_apply]
  congr 1

/-- The actual affine restriction is scalar extension over the original
coordinate-ring restriction. -/
def affineOpenRestrictionSectionsIso [M.IsQuasicoherent] :
    (ModuleCat.extendScalars (X.presheaf.map i.op).hom).obj
      (ModuleCat.of Γ(X, U) Γ(M, U)) ≅ ModuleCat.of Γ(X, V) Γ(M, V) :=
  (ModuleCat.extendScalars (X.presheaf.map i.op).hom).mapIso (affineChartΓIso U M).symm ≪≫
    affineRestrictGlobalSectionsIso (X.presheaf.map i.op) (M.restrict U.property.fromSpec) ≪≫
      affineChartRestrictionSectionsIso U V i M

/-- The scalar-extension comparison sends every unit tensor to the original
restriction of that section. -/
theorem affineOpenRestrictionSectionsIso_one_tmul [M.IsQuasicoherent]
    (m : Γ(M, U)) :
    (affineOpenRestrictionSectionsIso U V i M).hom
      ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U),(X.presheaf.map i.op).hom] m) = M.val.map i.op m := by
  change (affineChartRestrictionSectionsIso U V i M).hom
    ((affineRestrictGlobalSectionsIso (X.presheaf.map i.op)
      (M.restrict U.property.fromSpec)).hom
        ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U),(X.presheaf.map i.op).hom]
          (affineChartΓIso U M).inv m)) = _
  have hu := congrArg (fun k => k ((affineChartΓIso U M).inv m))
    (affineRestrictGlobalSectionsIso_unit (X.presheaf.map i.op)
      (M.restrict U.property.fromSpec))
  change (affineRestrictGlobalSectionsIso (X.presheaf.map i.op)
      (M.restrict U.property.fromSpec)).hom
        ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U),(X.presheaf.map i.op).hom]
          (affineChartΓIso U M).inv m) =
    (((restrictAdjunction (Spec.map (X.presheaf.map i.op))).unit.app
      (M.restrict U.property.fromSpec)).app ⊤) ((affineChartΓIso U M).inv m) at hu
  rw [hu, affineChartRestrictionSectionsIso_unit]
  exact congrArg (M.val.map i.op) ((affineChartΓIso U M).inv_hom_id_apply m)

end AlgebraicGeometry.Scheme.Modules
