/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Chart

/-! # Generation by sections on a larger affine open -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
open scoped ModuleCat.Algebra
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Maps out of affine restricted sections are determined by the original restriction unit. -/
theorem affineRestriction_linearMap_ext {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsOpenImmersion (Spec.map φ)] (M : (Spec R).Modules) [M.IsQuasicoherent]
    {L : Type u} [AddCommGroup L] [Module S L]
    (f g : moduleSpecΓFunctor.obj (M.restrict (Spec.map φ)) →ₗ[S] L)
    (h : ∀ m : moduleSpecΓFunctor.obj M,
      f ((((restrictAdjunction (Spec.map φ)).unit.app M).app ⊤) m) =
        g ((((restrictAdjunction (Spec.map φ)).unit.app M).app ⊤) m)) : f = g := by
  let e := affineRestrictGlobalSectionsIso φ M
  let f' : moduleSpecΓFunctor.obj (M.restrict (Spec.map φ)) ⟶ ModuleCat.of S L :=
    ConcreteCategory.ofHom (C := ModuleCat S) f
  let g' : moduleSpecΓFunctor.obj (M.restrict (Spec.map φ)) ⟶ ModuleCat.of S L :=
    ConcreteCategory.ofHom (C := ModuleCat S) g
  have he : e.hom ≫ f' = e.hom ≫ g' := by
    apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit]
    simp only [Functor.map_comp, ← Category.assoc]
    simp only [e, affineRestrictGlobalSectionsIso_unit]
    ext m
    exact h m
  exact ModuleCat.hom_ext_iff.mp ((cancel_epi e.hom).mp he)

/-- Maps on a smaller affine open are determined by restrictions from the larger affine open. -/
theorem affineOpenRestriction_linearMap_ext {X : Scheme.{u}} (U V : X.affineOpens)
    (i : V.val ⟶ U.val) (M : X.Modules) [M.IsQuasicoherent]
    {L : Type u} [AddCommGroup L] [Module Γ(X, V) L]
    (f g : Γ(M, V) →ₗ[Γ(X, V)] L)
    (h : ∀ m : Γ(M, U), f (M.val.map i.op m) = g (M.val.map i.op m)) : f = g := by
  let φ : Γ(X, U) ⟶ Γ(X, V) := X.presheaf.map i.op
  have hc : Spec.map φ ≫ U.property.fromSpec = V.property.fromSpec :=
    U.property.map_fromSpec V.property i.op
  have : IsOpenImmersion (Spec.map φ ≫ U.property.fromSpec) := hc ▸ inferInstance
  have : IsOpenImmersion (Spec.map φ) :=
    IsOpenImmersion.of_comp (Spec.map φ) U.property.fromSpec
  let e := moduleSpecΓFunctor.mapIso
    (((restrictFunctorComp (Spec.map φ) U.property.fromSpec).symm.app M) ≪≫
      (restrictFunctorCongr hc).app M) ≪≫ affineChartΓIso V M
  have he : f.comp e.toLinearEquiv.toLinearMap = g.comp e.toLinearEquiv.toLinearMap := by
    apply affineRestriction_linearMap_ext φ (M.restrict U.property.fromSpec)
    intro m
    have hm : e.hom
        ((((restrictAdjunction (Spec.map φ)).unit.app
          (M.restrict U.property.fromSpec)).app ⊤) m) =
        M.val.map i.op ((affineChartΓIso U M).hom m) := by
      change Γ(M, U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) at m
      change (affineChartΓIso V M).hom
        ((((restrictFunctorCongr hc).hom.app M).app ⊤)
          ((((restrictFunctorComp (Spec.map φ) U.property.fromSpec).inv.app M).app ⊤)
            ((((restrictAdjunction (Spec.map φ)).unit.app
              (M.restrict U.property.fromSpec)).app ⊤) m))) = _
      rw [restrictFunctorCongr_hom_app_app, restrictFunctorComp_inv_app_app,
        restrictAdjunction_unit_app_app]
      rw [restrict_map]
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
    change f (e.hom _) = g (e.hom _)
    rw [hm]
    exact h _
  apply LinearMap.ext
  intro m
  obtain ⟨m, rfl⟩ := e.toLinearEquiv.surjective m
  exact LinearMap.congr_fun he m

/-- Original restriction images span sections on every smaller affine open. -/
theorem affineOpenRestriction_span {X : Scheme.{u}} (U V : X.affineOpens)
    (i : V.val ⟶ U.val) (M : X.Modules) [M.IsQuasicoherent] :
    Submodule.span Γ(X, V) (Set.range (M.val.map i.op)) = ⊤ := by
  let P := Submodule.span Γ(X, V) (Set.range (M.val.map i.op))
  have h : P.mkQ = 0 := affineOpenRestriction_linearMap_ext U V i M P.mkQ 0
    (fun m => by
      exact (Submodule.Quotient.mk_eq_zero P).mpr (Submodule.subset_span ⟨m, rfl⟩))
  apply top_unique
  intro m _
  exact (Submodule.Quotient.mk_eq_zero P).mp (LinearMap.congr_fun h m)

end AlgebraicGeometry.Scheme.Modules
