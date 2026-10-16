/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimension identities for original module short complexes

The original homology of a short complex over a field has dimension equal
to that of the middle term minus the dimensions of the two differential
images. Only the middle term need be finite. With finite third term, an
equivalent identity uses original opcycles and the original second cokernel.
These identities apply to residue-field complexes before any base-change
isomorphism for homology is known.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module

namespace CategoryTheory.ShortComplex

universe u v

variable {K : Type u} [Field K] (S : ShortComplex (ModuleCat.{v} K))

/-- Actual homology plus the two actual differential-image dimensions equals the middle
dimension. Finiteness of the source or third term is not required. -/
theorem finrank_homology_add_finrank_ranges [Module.Finite K S.X₂] :
    finrank K S.homology + finrank K S.f.hom.range + finrank K S.g.hom.range =
      finrank K S.X₂ := by
  have hmap : S.moduleCatToCycles.range.map S.g.hom.ker.subtype = S.f.hom.range := by
    rw [← LinearMap.range_comp]
    rfl
  have hr := (Submodule.equivMapOfInjective S.g.hom.ker.subtype
    Subtype.val_injective S.moduleCatToCycles.range).finrank_eq
  rw [hmap] at hr
  have hh : finrank K S.homology =
      finrank K (S.g.hom.ker ⧸ S.moduleCatToCycles.range) :=
    S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  have hq := S.moduleCatToCycles.range.finrank_quotient_add_finrank
  have hn := S.g.hom.finrank_range_add_finrank_ker
  omega

/-- Original homology and the third term balance the original opcycles and second
cokernel. This form is useful for fibrewise semicontinuity. -/
theorem finrank_homology_add_finrank_eq_opcycles_add_cokernel
    [Module.Finite K S.X₂] [Module.Finite K S.X₃] :
    finrank K S.homology + finrank K S.X₃ =
      finrank K S.opcycles + finrank K (cokernel S.g : ModuleCat.{v} K) := by
  have hh := S.finrank_homology_add_finrank_ranges
  have hf := S.f.hom.range.finrank_quotient_add_finrank
  have hg := S.g.hom.range.finrank_quotient_add_finrank
  have hp : finrank K S.opcycles = finrank K (S.X₂ ⧸ S.f.hom.range) :=
    S.moduleCatOpcyclesIso.toLinearEquiv.finrank_eq
  have hc : finrank K (cokernel S.g : ModuleCat.{v} K) =
      finrank K (S.X₃ ⧸ S.g.hom.range) :=
    (ModuleCat.cokernelIsoRangeQuotient S.g).toLinearEquiv.finrank_eq
  omega

end CategoryTheory.ShortComplex
