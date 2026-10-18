/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FieldFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverPreservation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverDirectSummands
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! Actual Galois-category and identity-point fibre-functor dictionaries
over a separably closed field. The general connected-base case is separate. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)

universe u
variable (K : Type u) [Field K] [IsSepClosed K]

private theorem finiteTypesHaveGroupQuotients (G : Type u) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) FintypeCat.{u} := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

instance instClosedFieldPreGalois : PreGaloisCategory
    (Scheme.FiniteEtale (Spec (CommRingCat.of K))) where
  hasQuotientsByFiniteGroups G _ _ := by
    have := finiteTypesHaveGroupQuotients G
    exact Adjunction.hasColimitsOfShape_of_equivalence
      (fiberToFinite (𝟙 (Spec (CommRingCat.of K))))
  monoInducesIsoOnDirectSummand {_ _} i _ := coverMonoInducesIsoOnDirectSummand i

instance instClosedFieldFiberFunctor :
    PreGaloisCategory.FiberFunctor (fiberToFinite (𝟙 (Spec (CommRingCat.of K)))) where
  preservesQuotientsByFiniteGroups _ _ _ := by infer_instance

instance instClosedFieldGalois : GaloisCategory (Scheme.FiniteEtale (Spec (CommRingCat.of K))) where
  hasFiberFunctor := ⟨fiberToFinite (𝟙 (Spec (CommRingCat.of K))), inferInstance⟩

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 d4fe378416a07d385981445bff5b7296a906c969c67cb8e65bdd4e877ca98d4b.
Definitions, hypotheses and universes are retained modulo native names. -/
