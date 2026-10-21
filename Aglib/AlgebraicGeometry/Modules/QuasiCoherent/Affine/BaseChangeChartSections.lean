/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeChart
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections

/-!
# Actual pullback sections in tensor-coordinate charts

The ambient pullback coefficient on each literal tensor affine chart has the
native scalar-extension presentation of the original coefficient sections.
All maps are the original pullback, open restriction and affine counit maps.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

open Scheme.AffineBaseChange

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B)))
  (M : X.Modules)

/-- Actual restriction of the ambient pullback to a tensor chart is the
pullback of the original affine restriction. -/
def tensorChartPullbackIso :
    ((pullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap A C))))).obj M).restrict
        (tensorChartMap (C := C) f j hj) ≅
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] C))))).obj
        (M.restrict j) :=
  (pullbackOpenSquare (tensorChartMap (C := C) f j hj)
    (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] C))))
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A C)))) j
    (tensorChartMap_fst f j hj)).app M

/-- Tensor-chart sections of the actual ambient pullback are obtained by
extending the original affine section module along the left inclusion. -/
def tensorChartPullbackSectionsIso [M.IsQuasicoherent] :
    (ModuleCat.extendScalars (algebraMap B (B ⊗[A] C))).obj
      (moduleSpecΓFunctor.obj (M.restrict j)) ≅
      moduleSpecΓFunctor.obj
        (((pullback (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap A C))))).obj M).restrict
            (tensorChartMap (C := C) f j hj)) :=
  affinePullbackGlobalSectionsIso
      (CommRingCat.ofHom (algebraMap B (B ⊗[A] C))) (M.restrict j) ≪≫
    moduleSpecΓFunctor.mapIso (tensorChartPullbackIso f j hj M).symm

end AlgebraicGeometry.Scheme.Modules
