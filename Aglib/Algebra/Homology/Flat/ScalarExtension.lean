/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.CochainComplex.MapTruncation
public import Aglib.Algebra.Homology.Flat.Kernel

/-!
# Canonical scalar extension of the original good truncation

Universal tensor exactness proves preservation of the original boundary
kernel after every scalar extension. The generic native truncation comparison
therefore supplies an actual chain isomorphism, its original inclusion equation
and coefficient naturality. The original mapped inclusion is a quasi-isomorphism
under the actual upper cohomological bound after scalar extension.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CochainComplex

variable {R : Type u} {B : Type w} [CommRing R] [CommRing B]
  (σ : R →+* B) (K : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ)
  [Module.Flat R (K.X (b + 1))] [Module.Flat R (K.X (b + 2))]

/-- Every ring base change preserves the actual boundary kernel, as a proved
consequence of original term flatness and universal next-degree tensor exactness. -/
theorem extendScalars_preserves_boundaryKernel
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N)) :
    PreservesLimit (parallelPair (K.d b (b + 1)) 0)
      (ModuleCat.extendScalars.{u, w, v} σ) := by
  let S := K.sc' b (b + 1) (b + 2)
  let : Module.Flat R S.X₂ := by
    change Module.Flat R (K.X (b + 1))
    infer_instance
  let : Module.Flat R S.X₃ := by
    change Module.Flat R (K.X (b + 2))
    infer_instance
  exact S.extendScalars_preservesKernel_of_universally_lTensor_exact σ h

/-- The original good truncation commutes with arbitrary native scalar
extension. This is the existing generic comparison with its kernel hypothesis
proved by universal tensor exactness; no new base-change map is constructed. -/
def extendScalarsTruncLEIso
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N)) :
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj (K.truncLE b) ≅
      CochainComplex.truncLE
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj K) b := by
  letI := extendScalars_preserves_boundaryKernel σ K b h
  exact K.mapTruncLEIso (ModuleCat.extendScalars σ) b

/-- The scalar-extension comparison retains the original mapped inclusion. -/
@[reassoc (attr := simp)]
theorem extendScalarsTruncLEIso_hom_ιTruncLE
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N)) :
    (extendScalarsTruncLEIso σ K b h).hom ≫
        CochainComplex.ιTruncLE
          (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj K) b =
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE b) := by
  let := extendScalars_preserves_boundaryKernel σ K b h
  exact K.mapTruncLEIso_hom_ιTruncLE (ModuleCat.extendScalars σ) b

/-- Original coefficient maps commute with the same scalar-extension
comparison when both following tensor degrees are universally exact. -/
@[reassoc]
theorem extendScalarsTruncLEIso_hom_naturality
    (hK : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N))
    {L : CochainComplex (ModuleCat.{v} R) ℤ}
    [Module.Flat R (L.X (b + 1))] [Module.Flat R (L.X (b + 2))] (φ : K ⟶ L)
    (hL : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((L.d b (b + 1)).hom.lTensor N)
        ((L.d (b + 1) (b + 2)).hom.lTensor N)) :
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.truncLEMap φ b) ≫ (extendScalarsTruncLEIso σ L b hL).hom =
      (extendScalarsTruncLEIso σ K b hK).hom ≫ CochainComplex.truncLEMap
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map φ) b := by
  let := extendScalars_preserves_boundaryKernel σ K b hK
  let := extendScalars_preserves_boundaryKernel σ L b hL
  exact K.mapTruncLEIso_hom_naturality (ModuleCat.extendScalars σ) b φ

/-- The actual mapped truncation inclusion is a quasi-isomorphism under the
actual base-changed upper cohomological bound, for every ring homomorphism. -/
theorem quasiIso_extendScalars_ιTruncLE_of_universally_lTensor_exact
    [CochainComplex.IsLE
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj K) b]
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N)) :
    QuasiIso (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map (K.ιTruncLE b)) := by
  let := extendScalars_preserves_boundaryKernel σ K b h
  exact K.quasiIso_map_ιTruncLE_of_isLE (ModuleCat.extendScalars σ) b

end CochainComplex
