/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Stages
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Exhaustion of the acyclic subobject stages

The native subobject type is small in the Grothendieck universe. Iterating
strict growth over a larger cardinal cannot be injective, so native transfinite
iteration reaches the top subobject. Exhaustiveness is proved, not postulated.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic)

lemma acyclicStages_top_mem_range {J : Type w} [LinearOrder J] [OrderBot J]
    [SuccOrder J] [WellFoundedLT J]
    (hJ : HasCardinalLT (Subobject M) (Cardinal.mk J)) :
    ∃ j : J, acyclicStages hG M hM j = ⊤ :=
  top_mem_range_transfiniteIterate (acyclicGrowth hG M hM) ⊥
    (lt_acyclicGrowth hG M hM) (acyclicGrowth_top hG M hM)
    (fun h ↦ by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)

/-- Some small ordinal stage reaches the entire original acyclic complex. -/
lemma exists_acyclic_filtration_ordinal :
    ∃ (o : Ordinal.{w}) (j : o.ToType),
      transfiniteIterate (acyclicGrowth hG M hM) j ⊥ = ⊤ := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject M)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ.ord, acyclicStages_top_mem_range hG M hM
    (lt_of_lt_of_le (Order.lt_succ _) (by simp [κ]))⟩

/-- A fixed small ordinal for the actual exhaustive source filtration. -/
def acyclicFiltrationOrdinal : Ordinal.{w} :=
  (exists_acyclic_filtration_ordinal hG M hM).choose

/-- The well-ordered small stage type of the exhaustive filtration. -/
abbrev acyclicFiltrationIndex : Type w := (acyclicFiltrationOrdinal hG M hM).ToType

/-- A stage at which the actual filtration has reached the original complex. -/
def acyclicFiltrationEndpoint : acyclicFiltrationIndex hG M hM :=
  (exists_acyclic_filtration_ordinal hG M hM).choose_spec.choose

instance : Nonempty (acyclicFiltrationIndex hG M hM) :=
  ⟨acyclicFiltrationEndpoint hG M hM⟩

noncomputable instance : OrderBot (acyclicFiltrationIndex hG M hM) :=
  WellFoundedLT.toOrderBot _

lemma acyclicFiltrationEndpoint_eq_top :
    acyclicStages hG M hM (acyclicFiltrationEndpoint hG M hM) = ⊤ :=
  (exists_acyclic_filtration_ordinal hG M hM).choose_spec.choose_spec

end CochainComplex
