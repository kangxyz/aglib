/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Affine
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Restriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback

/-!
# The affine comparison on an open cartesian square

The unit formula identifies the actual affine nonflat comparison with the
original higher-image open-restriction isomorphism. All section and cohomology
comparisons are the original ones.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology

set_option maxRecDepth 2000 in
-- The original open-restriction section formula carries the native and Ext scalar actions.
/-- The nonflat affine comparison on an actual open cartesian square is the installed
higher-image open-restriction map, through the native restriction/pullback identification. -/
theorem higherDirectImageAffineMap_eq_openRestriction
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (p : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R) (σ : R ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
    [IsOpenImmersion p] [IsOpenImmersion (Spec.map σ)]
    (h : IsPullback p b f (Spec.map σ)) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    higherDirectImageAffineMap (M := M) (N := M.restrict p) p b f σ h.w
        ((restrictAdjunction p).unit.app M) n =
      (restrictFunctorIsoPullback (Spec.map σ)).inv.app
          (((pushforward f).rightDerived n).obj M) ≫
        (higherDirectImageOpenRestrictionIso p b f (Spec.map σ) h n).hom.app M := by
  let E := ((pushforward f).rightDerived n).obj M
  let : E.IsQuasicoherent := moduleHigherDirectImageAffine_isQuasicoherent f M n
  symm
  apply higherDirectImageAffineMap_eq_of_one_tmul (M := M) (N := M.restrict p)
    p b f σ h.w ((restrictAdjunction p).unit.app M) n
  dsimp only
  intro x
  rw [affinePullbackGlobalSectionsIso_one_tmul]
  have hu : (pullbackPushforwardAdjunction (Spec.map σ)).unit.app E ≫
      (pushforward (Spec.map σ)).map
        ((restrictFunctorIsoPullback (Spec.map σ)).inv.app E) =
      (restrictAdjunction (Spec.map σ)).unit.app E :=
    restrictFunctorIsoPullback_inv_adjunction_unit (Spec.map σ) E
  have hx := congrArg
    (fun t : E ⟶ (pushforward (Spec.map σ)).obj (E.restrict (Spec.map σ)) => t.app ⊤ x) hu
  change ((restrictFunctorIsoPullback (Spec.map σ)).inv.app E).app ⊤
      (((pullbackPushforwardAdjunction (Spec.map σ)).unit.app E).app ⊤ x) =
    ((restrictAdjunction (Spec.map σ)).unit.app E).app ⊤ x at hx
  change moduleHigherDirectImageAffineSectionsLinearEquiv b (M.restrict p)
      (injectiveResolution (M.restrict p)) n
      (moduleSpecΓFunctor.map
        ((higherDirectImageOpenRestrictionIso p b f (Spec.map σ) h n).hom.app M)
        (((restrictFunctorIsoPullback (Spec.map σ)).inv.app E).app ⊤
          (((pullbackPushforwardAdjunction (Spec.map σ)).unit.app E).app ⊤ x))) = _
  rw [hx]
  exact moduleHigherDirectImageAffineSectionsLinearEquiv_openRestriction p b f σ h M
    (injectiveResolution M) (injectiveResolution (M.restrict p)) n x

end AlgebraicGeometry.Scheme.Modules
