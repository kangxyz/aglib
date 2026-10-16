/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology.Forget
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Geometric

/-!
# Canonical tensor maps on actual module Cech homology

The native homology scalar-extension mate followed by an actual Cech complex
map gives the tensor map on Cech homology. A geometric unit square identifies
its unit-pure-tensor formula with the unchanged additive geometric Cech map.
This comparison retains the supplied complex map and equality explicitly;
the geometric base-change construction supplies them separately.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  {X Y : Scheme.{u}} (p : X ⟶ Y) (σ : R →+* S)
  (α : R →+* Γ(Y, ⊤)) (β : S →+* Γ(X, ⊤))
  {M : Y.Modules} {N : X.Modules} {ι : Type u} (U : ι → Y.Opens)

variable
  (δ : ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℕ)).obj
      (moduleCechComplex Y α M U) ⟶
    moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i))

/-- Native scalar extension of homology followed by the original module Cech map. -/
def moduleCechTensorHomologyMap (n : ℕ) :
    (ModuleCat.extendScalars σ).obj ((moduleCechComplex Y α M U).homology n) ⟶
      (moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)).homology n :=
  extendScalarsHomologyMap σ (moduleCechComplex Y α M U) n ≫ homologyMap δ n

/-- Exact scalar extension and a genuine complex isomorphism give an isomorphism on homology. -/
theorem moduleCechTensorHomologyMap_isIso
    [(ModuleCat.extendScalars.{u, u, u} σ).PreservesHomology] [IsIso δ] (n : ℕ) :
    IsIso (moduleCechTensorHomologyMap p σ α β U δ n) := by
  unfold moduleCechTensorHomologyMap extendScalarsHomologyMap
  rw [ModuleCat.homologyBaseChangeMap_eq_mapHomologyIso_inv]
  infer_instance

variable (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
  (hδ : (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsForgetUnit σ) (.up ℕ)).app
          (moduleCechComplex Y α M U) ≫
        ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).map δ ≫
        (moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).hom =
      (moduleCechForgetIso Y α M U).hom ≫
        additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
          (moduleCoefficientPullback p φ))

include hδ
set_option maxHeartbeats 800000 in
-- Native scalar restriction and Cech products require extra normalization in this comparison.
/-- The actual Cech tensor map on a unit pure tensor is the actual additive geometric map. -/
theorem moduleCechTensorHomologyMap_one_tmul (n : ℕ)
    (x : (moduleCechComplex Y α M U).homology n) :
    (moduleCechAdditiveHomologyIso X β N (fun i => p ⁻¹ᵁ U i) n).hom
        (moduleCechTensorHomologyMap p σ α β U δ n ((1 : S) ⊗ₜ[R,σ] x)) =
      homologyMap (additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
        (moduleCoefficientPullback p φ)) n
          ((moduleCechAdditiveHomologyIso Y α M U n).hom x) := by
  have h := ModuleCat.extendScalarsForgetUnit_homology_map_of_square σ
    (moduleCechComplex Y α M U) n (moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i)) δ
    (moduleCechForgetIso Y α M U).hom
    (moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).hom
    (additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
      (moduleCoefficientPullback p φ)) hδ
  have hx := ConcreteCategory.congr_hom h x
  simp only [Functor.map_comp, ConcreteCategory.comp_apply,
    ModuleCat.extendScalarsForgetUnit_app_apply] at hx
  dsimp only [moduleCechAdditiveHomologyIso, moduleCechTensorHomologyMap,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact hx

end AlgebraicGeometry.Scheme.Cohomology
