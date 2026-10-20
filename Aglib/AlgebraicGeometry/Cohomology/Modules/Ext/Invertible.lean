/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Aglib.AlgebraicGeometry.Modules.Tensor.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic

/-!
# Degree-zero Ext out of an invertible module

The original dual-tensor map preserves structural scalars. Consequently
`Ext⁰(L,M)` is linearly equivalent to the actual `H⁰(M tensor L.dual)` on an
arbitrary field scheme, for its original structural field action.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {K : Type u} [Field K] (Y : FScheme K)

/-- The actual dual-tensor equivalence preserves the field action induced by
`Y.hom`; no scalar action is transported from another vector space. -/
instance lineBundleDualTensorEquivalence_linear (L : LineBundle Y.left) :
    letI := moduleCategoryLinearOfHom Y.left (Scheme.constants Y)
    Functor.Linear K (lineBundleDualTensorEquivalence Y.left L).functor := by
  let := moduleCategoryLinearOfHom Y.left (Scheme.constants Y)
  change Functor.Linear K (moduleTensorLeftFunctor Y.left (dualLineBundle Y.left L).val)
  infer_instance

/-- Morphisms out of the original line bundle are actual sections of the
original coefficient tensored with its dual, with structural K-linearity. -/
def lineBundleHomSectionsEquiv (L : LineBundle Y.left) (M : Y.left.Modules) :
    letI := moduleCategoryLinearOfHom Y.left (Scheme.constants Y)
    (@Quiver.Hom Y.left.Modules _ L.val M) ≃ₗ[K]
      (tensorSheaf Y.left M (dualLineBundle Y.left L).val).val.obj (op ⊤) := by
  letI := moduleCategoryLinearOfHom Y.left (Scheme.constants Y)
  let F := (lineBundleDualTensorEquivalence Y.left L).functor
  letI : F.Additive := by
    change (moduleTensorLeftFunctor Y.left (dualLineBundle Y.left L).val).Additive
    infer_instance
  let e : (@Quiver.Hom Y.left.Modules _ L.val M) ≃ₗ[K]
      (F.obj L.val ⟶ F.obj M) :=
    LinearEquiv.ofBijective (F.mapLinearMap K)
      ⟨F.map_injective, F.map_surjective⟩
  exact e.trans ((CategoryTheory.Linear.homCongr K (C := Y.left.Modules)
    (dualEvaluationIso Y.left L)
    (tensorSheafBraiding Y.left (dualLineBundle Y.left L).val M)).trans
      (unitHomGlobalSectionsLinearEquivOfHom Y.left (Scheme.constants Y)
        (tensorSheaf Y.left M (dualLineBundle Y.left L).val)))

/-- The actual degree-zero Ext group is the actual degree-zero cohomology of
`M tensor L.dual`, linearly for the original structural K-action. -/
def lineBundleExtZeroEquivH0 (L : LineBundle Y.left) (M : Y.left.Modules) :
    letI := moduleCategoryLinearOfHom Y.left (Scheme.constants Y)
    Ext.{u + 1} (C := Y.left.Modules) L.val M 0 ≃ₗ[K]
      moduleCohomology K Y (tensorSheaf Y.left M (dualLineBundle Y.left L).val) 0 := by
  letI := moduleCategoryLinearOfHom Y.left (Scheme.constants Y)
  exact (Ext.linearEquiv₀ (R := K)).trans
    ((lineBundleHomSectionsEquiv Y L M).trans
      (moduleH0Equiv Y (tensorSheaf Y.left M (dualLineBundle Y.left L).val)).symm)

end AlgebraicGeometry.Scheme.Cohomology
