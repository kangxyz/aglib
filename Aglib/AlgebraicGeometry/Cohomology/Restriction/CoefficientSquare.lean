/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Coefficients
public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer.RestrictionCoefficientSquare

/-! # Complete original open-restriction coefficient squares

The original coefficient maps and comparisons are constructed together using
the canonical public geometric law. The canonical pointwise coefficient laws
remain in Restriction.Coefficients unchanged.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The complete actual module open-restriction coefficient square. Its edges
are the original open comparison, coefficient map, geometric postcomposition
and whole-space comparison, with their original law constructed together. -/
def moduleOpenRestrictionCoefficientSquare (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) {N : U.toScheme.Modules} (ε : M.restrict U.ι ⟶ N)
    (n : ℕ) : Square AddCommGrpCat.{u + 1} := by
  let a := U.ι
  let η := (Scheme.Modules.restrictAdjunction a).unit.app M
  exact TopCat.Sheaf.openCohomologyRestrictionCoefficientSquare.{u, u + 1} a.base
    (moduleCoefficientPullback a η)
    (moduleCoefficientPullback a (η ≫ (Scheme.Modules.pushforward a).map ε))
    ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map ε)
    (moduleCoefficientPullback_postcomp a η ε) n U U.ι_preimage_self
    (AddCommGrpCat.ofHom
      (sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n).toAddMonoidHom)
    (moduleHPrimeOpenRestrictionAddEquiv_geometric X U M n)


/-- An actual local coefficient arrow acts on the original open comparison by
the original geometric map of the postcomposed restriction unit. The four
transparent edges are those of the same complete native square. -/
theorem moduleOpenRestrictionCoefficientSquare_apply (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) {N : U.toScheme.Modules} (ε : M.restrict U.ι ⟶ N)
    (n : ℕ) (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :
    (moduleOpenRestrictionCoefficientSquare X U M ε n).f₂₄
        ((moduleOpenRestrictionCoefficientSquare X U M ε n).f₁₂ x) =
      (moduleOpenRestrictionCoefficientSquare X U M ε n).f₃₄
        ((moduleOpenRestrictionCoefficientSquare X U M ε n).f₁₃ x) :=
  ConcreteCategory.congr_hom (moduleOpenRestrictionCoefficientSquare X U M ε n).fac x

end AlgebraicGeometry.Scheme.Cohomology
