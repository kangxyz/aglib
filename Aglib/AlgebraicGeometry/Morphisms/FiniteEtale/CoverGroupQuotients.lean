/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteActionSheafColimit
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverDirectSummands
public import Mathlib.CategoryTheory.Galois.Basic

/-! Arbitrary finite-group quotients in actual finite-etale covers, conditional
only on the displayed 03RV existence theorem. The finite action need not be free.
Group universes are resized using the pinned finite-group equivalence. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable {X : Scheme.{u}}

theorem coverHasSmallFiniteGroupQuotients (hRV : Stacks03RV X)
    (G : Type) [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) (Scheme.FiniteEtale X) := by
  classical
  let := Fintype.ofFinite G
  exact ⟨fun D => hasCoverColimitOfFiniteLocalConstancy D hRV
    (finiteActionSheafColimit_isFiniteLocallyConstant D)⟩

theorem coverHasFiniteGroupQuotients (hRV : Stacks03RV X)
    (G : Type u) [Group G] [Finite G] : HasColimitsOfShape (SingleObj G)
      (Scheme.FiniteEtale X) := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  let := coverHasSmallFiniteGroupQuotients hRV G'
  exact hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

theorem coverSectionSheaf_preservesSmallFiniteGroupQuotients (hRV : Stacks03RV X)
    (G : Type) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (finiteCoverSectionSheafFunctor X) := by
  classical
  let := Fintype.ofFinite G
  refine ⟨fun {D} => ?_⟩
  let := coverCreatesColimitOfFiniteLocalConstancy D hRV
    (finiteActionSheafColimit_isFiniteLocallyConstant D)
  infer_instance

theorem coverSectionSheaf_preservesFiniteGroupQuotients (hRV : Stacks03RV X)
    (G : Type u) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (finiteCoverSectionSheafFunctor X) := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  let := coverSectionSheaf_preservesSmallFiniteGroupQuotients hRV G'
  exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm _

/-- The actual cover category over every scheme satisfies the exact pinned
PreGaloisCategory fields once 03RV is supplied. All quotient construction and
universal-property obligations are proved here, rather than passed as premises. -/
theorem coverPreGaloisOfStacks03RV (hRV : Stacks03RV X) : PreGaloisCategory
    (Scheme.FiniteEtale X) where
  hasQuotientsByFiniteGroups G _ _ := coverHasFiniteGroupQuotients hRV G
  monoInducesIsoOnDirectSummand {_ _} i _ := coverMonoInducesIsoOnDirectSummand i

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ac7f1babf8aa8c2fae177217e7d82b8d7584e8f8572b346e60a616741cb6a593.
Definitions, hypotheses and universes are retained modulo native names. -/
