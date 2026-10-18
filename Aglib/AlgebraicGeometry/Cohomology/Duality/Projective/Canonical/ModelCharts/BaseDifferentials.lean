/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.BaseComparison
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.TopRestriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.IsomorphicCharts

/-!
# Original differential factors under a change of affine base

The original identity restriction and the original exterior restriction
have the same unit. Consequently the original top-differential maps paste
with the exterior power of the actual identity-source base comparison.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem exteriorRestrictionIdentity (Z : Scheme.{u}) (M : Z.Modules) (m : ℕ) :
    (moduleExteriorPowerFunctor Z m).map (restrictFunctorId.inv.app M) ≫
        (moduleExteriorPowerRestrictionIso (𝟙 Z) M m).hom =
      restrictFunctorId.inv.app (moduleExteriorPower Z M m) := by
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext Z.sheaf M
    ((moduleExteriorPower Z M m).restrict (𝟙 Z)) m
  intro U v
  change (moduleExteriorPowerRestrictionIso (𝟙 Z) M m).hom.val.app U
      (((moduleExteriorPowerFunctor Z m).map (restrictFunctorId.inv.app M)).val.app U
        ((SheafOfModulesOfCommRing.exteriorPowerMk Z.sheaf M m).app U v)) =
    (restrictFunctorId.inv.app (moduleExteriorPower Z M m)).val.app U
      ((SheafOfModulesOfCommRing.exteriorPowerMk Z.sheaf M m).app U v)
  have h₁ := congrArg ((moduleExteriorPowerRestrictionIso (𝟙 Z) M m).hom.val.app U)
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk Z.sheaf
      (restrictFunctorId.inv.app M) m U v)
  have h₂ := moduleExteriorPowerRestrictionIso_hom_mk (𝟙 Z) M m U.unop
    (fun k => (restrictFunctorId.inv.app M).val.app U (v k))
  let e : 𝟙 Z ''ᵁ U.unop = U.unop := by simp
  have h₃ := SheafOfModulesOfCommRing.exteriorPowerMk_naturality Z.sheaf M m
    (eqToHom e).op v
  exact h₁.trans (h₂.trans h₃.symm)

/-- The original top map on an identity-source base square is the exterior base map
after the original identity restriction. -/
theorem canonicalTopDifferentialRestriction_identity
    {Z Y Y' : Scheme.{u}} (f : Z ⟶ Y) (g : Z ⟶ Y') (j : Y' ⟶ Y)
    [IsOpenImmersion j] (h : 𝟙 Z ≫ f = g ≫ j) (m : ℕ) :
    restrictFunctorId.inv.app (moduleExteriorPower Z (relativeDifferentialSheaf f) m) ≫
        (relativeTopDifferentialRestrictionIso f (𝟙 Z) g j h m).hom =
      ((moduleExteriorPowerFunctor Z m).mapIso
        (restrictFunctorId.symm.app (relativeDifferentialSheaf f) ≪≫
          relativeDifferentialOpenSquareIso f (𝟙 Z) g j h)).hom := by
  rw [← exteriorRestrictionIdentity Z (relativeDifferentialSheaf f) m]
  change (_ ≫ (moduleExteriorPowerRestrictionIso (𝟙 Z)
      (relativeDifferentialSheaf f) m).hom) ≫
      ((moduleExteriorPowerRestrictionIso (𝟙 Z) (relativeDifferentialSheaf f) m).inv ≫ _) =
    (moduleExteriorPowerFunctor Z m).map (_ ≫ _)
  rw [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]

private theorem restrictionLeftIdentity {U X : Scheme.{u}}
    (a : U ⟶ X) [IsOpenImmersion a] (M : X.Modules) :
    (restrictFunctorCongr (Category.id_comp a).symm).hom.app M ≫
        (restrictFunctorComp (𝟙 U) a).hom.app M =
      restrictFunctorId.inv.app (M.restrict a) := by
  apply Scheme.Modules.hom_ext
  intro V
  simp only [Scheme.Modules.Hom.comp_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorComp_hom_app_app, restrictFunctorId_inv_app_app]
  change M.presheaf.map _ ≫ M.presheaf.map _ = M.presheaf.map _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

/-- The original coefficient comparison pastes across an actual identity-source
base square, including its genuine exterior degree. -/
theorem canonicalTopDifferentialRestrictionInDegree_base
    {X Z Y Y₀ Y₁ : Scheme.{u}}
    (p : X ⟶ Y) (a : Z ⟶ X) (q₀ : Z ⟶ Y₀) (j₀ : Y₀ ⟶ Y)
    (q₁ : Z ⟶ Y₁) (j₁ : Y₁ ⟶ Y₀)
    [IsOpenImmersion a] [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (h₀ : a ≫ p = q₀ ≫ j₀) (h₁ : 𝟙 Z ≫ q₀ = q₁ ≫ j₁)
    (h : a ≫ p = q₁ ≫ (j₁ ≫ j₀)) (n m : ℕ) (hnm : n = m) :
    (canonicalTopDifferentialRestrictionInDegree p a q₀ j₀ h₀ n m hnm).hom ≫
        ((moduleExteriorPowerFunctor Z m).mapIso
          (restrictFunctorId.symm.app (relativeDifferentialSheaf q₀) ≪≫
            relativeDifferentialOpenSquareIso q₀ (𝟙 Z) q₁ j₁ h₁)).hom =
      (canonicalTopDifferentialRestrictionInDegree p a q₁ (j₁ ≫ j₀) h n m hnm).hom := by
  let E := canonicalTopDifferentialRestrictionInDegree p a q₀ j₀ h₀ n m hnm
  have H : (𝟙 Z ≫ a) ≫ p = q₁ ≫ (j₁ ≫ j₀) := by
    simpa only [Category.id_comp] using h
  have hC := canonicalTopDifferentialRestrictionInDegree_comp p q₀ q₁ a j₀
    (𝟙 Z) j₁ h₀ h₁ H n m hnm
  have hG := canonicalTopDifferentialRestriction_congr p a (𝟙 Z ≫ a) q₁
    (j₁ ≫ j₀) h H (Category.id_comp a).symm n
  have hG' := congrArg (fun t => t ≫
    (eqToIso (congrArg (moduleExteriorPower Z (relativeDifferentialSheaf q₁)) hnm)).hom) hG
  have hC' := congrArg (fun t =>
    (restrictFunctorCongr (Category.id_comp a).symm).hom.app
      (moduleExteriorPower X (relativeDifferentialSheaf p) n) ≫ t) hC
  have hAll : restrictFunctorId.inv.app
        ((moduleExteriorPower X (relativeDifferentialSheaf p) n).restrict a) ≫
      (restrictFunctor (𝟙 Z)).map E.hom ≫
        (relativeTopDifferentialRestrictionIso q₀ (𝟙 Z) q₁ j₁ h₁ m).hom =
      (canonicalTopDifferentialRestrictionInDegree p a q₁ (j₁ ≫ j₀) h n m hnm).hom := by
    have hh := hC'.trans (by
      simpa only [canonicalTopDifferentialRestrictionInDegree, Iso.trans_hom,
        Category.assoc] using hG')
    simpa only [E, ← Category.assoc, restrictionLeftIdentity,
      canonicalTopDifferentialRestrictionInDegree, Iso.trans_hom, Functor.id_obj] using hh
  have hNat := restrictFunctorId.inv.naturality E.hom
  change E.hom ≫ restrictFunctorId.inv.app
      (moduleExteriorPower Z (relativeDifferentialSheaf q₀) m) =
    restrictFunctorId.inv.app
      ((moduleExteriorPower X (relativeDifferentialSheaf p) n).restrict a) ≫
        (restrictFunctor (𝟙 Z)).map E.hom at hNat
  have hId := canonicalTopDifferentialRestriction_identity q₀ q₁ j₁ h₁ m
  calc
    _ = E.hom ≫ restrictFunctorId.inv.app
        (moduleExteriorPower Z (relativeDifferentialSheaf q₀) m) ≫
          (relativeTopDifferentialRestrictionIso q₀ (𝟙 Z) q₁ j₁ h₁ m).hom := by
      simpa only [E, Category.assoc] using congrArg (fun t => E.hom ≫ t) hId.symm
    _ = _ := by
      simpa only [Category.assoc] using (congrArg
        (fun t => t ≫ (relativeTopDifferentialRestrictionIso q₀ (𝟙 Z) q₁ j₁ h₁ m).hom)
          hNat).trans hAll

end AlgebraicGeometry.Scheme.Modules
