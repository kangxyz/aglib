/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.CogeneratorCriterion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.Presentations
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.CohomologyColimits

/-! # Original local comparison from constructible finite embeddings

On a separated qcqs scheme, the actual positive genuine presentation supplies
all stages and both original coefficient colimits. Native qcqs cohomological
continuity supplies their source and target preservation. Only the geometric
finite embedding of a stage and original finite annihilator tests remain as
inputs to the comparison criterion.

The calculation uses the native standard Ext size internally. It does not
assert global finite cogeneration or proper base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

variable (X : Scheme.{u}) (n : ℕ)

/-- The actual filtered genuine coefficient presentation used by the local
criterion. Its point and all cocone maps are the original ones. -/
structure FiniteStagePresentation (M : Reduction.ZModSheaf X n) where
  /-- The original coefficient-sized index. -/
  index : Type (u + 1)
  /-- The original small category structure. -/
  category : SmallCategory index
  /-- The index is filtered. -/
  filtered : @IsFiltered index category
  /-- The genuine coefficient diagram. -/
  diagram : @Functor index category (Reduction.ZModSheaf X n) inferInstance
  /-- The original cocone has the given genuine module as point. -/
  legs : diagram ⟶ (Functor.const index).obj M
  /-- That actual cocone is colimiting. -/
  isColimit : IsColimit (Cocone.mk M legs)
  /-- Its actual stages satisfy the geometric finite conditions. -/
  stage : ∀ j, IsConstructibleFiniteStage X n (diagram.obj j)

/-- Choose the proved actual positive presentation, rather than a
presentation whose existence is an additional hypothesis. -/
def finiteStagePresentation [X.IsSeparated] (hn : n ≠ 0)
    (M : Reduction.ZModSheaf X n) : FiniteStagePresentation X n M := by
  apply Classical.choice
  obtain ⟨I, hI, hfiltered, D, κ, ⟨hc⟩, _, hstage⟩ :=
    exists_filtered_genuine_presentation_of_isSeparated X n hn M
  let := hI
  refine ⟨{
    index := I
    category := hI
    filtered := hfiltered
    diagram := D
    legs := κ
    isColimit := hc
    stage := ?_ }⟩
  intro j
  exact ⟨(hstage j).2.1, (hstage j).1, (hstage j).2.2⟩

section StandardExt

attribute [local instance] HasExt.standard

variable {X} [X.IsSeparated] [CompactSpace X] [QuasiSeparatedSpace X]
  {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (i : S ⟶ X)

/-- On separated qcqs source and qcqs target, geometric finite embeddings
and original finite annihilator tests imply the actual all-degree pullback
comparison. The presentation and cohomology preservation are produced here. -/
theorem cohomologyPullback_bijective_of_constructible_finiteEmbeddings
    (hn : n ≠ 0)
    (hfinite : ∀ M, IsConstructibleFiniteStage X n M →
      Nonempty (FiniteConstantProductEmbedding ((Reduction.zmodUnderlying X n).obj M)))
    (hzero : ∀ N, IsFiniteConstantAnnihilator X n N →
      Function.Injective (cohomologyPullback.{u, u + 2, u + 2} i
        ((Reduction.zmodUnderlying X n).obj N) 0))
    (htest : ∀ N, IsFiniteConstantAnnihilator X n N → ∀ q,
      Function.Surjective (cohomologyPullback.{u, u + 2, u + 2} i
        ((Reduction.zmodUnderlying X n).obj N) q))
    (M : Reduction.ZModSheaf X n) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} i
      ((Reduction.zmodUnderlying X n).obj M) q) := by
  let P (N : Reduction.ZModSheaf X n) := finiteStagePresentation X n hn N
  let J (N : Reduction.ZModSheaf X n) := (P N).index
  let : ∀ N, SmallCategory (J N) := fun N => (P N).category
  let : ∀ N, IsFiltered (J N) := fun N => (P N).filtered
  let : ∀ N, (colim : (J N ⥤ AddCommGrpCat.{u + 2}) ⥤
      AddCommGrpCat.{u + 2}).PreservesMonomorphisms := fun N => by
    let : HasExactColimitsOfShape (J N) AddCommGrpCat.{u + 2} :=
      hasExactFilteredColimitsOfShape_addCommGrpCat.{u + 1, u + 2} (J N)
    exact preservesMonomorphisms_of_preservesLimitsOfShape
      (colim : (J N ⥤ AddCommGrpCat.{u + 2}) ⥤ AddCommGrpCat.{u + 2})
  let K (N : Reduction.ZModSheaf X n) : J N ⥤ Reduction.ZModSheaf X n := (P N).diagram
  let κ (N : Reduction.ZModSheaf X n) : K N ⟶ (Functor.const (J N)).obj N := (P N).legs
  exact cohomologyPullback_bijective_of_finiteConstantAnnihilator_tests n i K κ
    (fun N => (P N).isColimit) (fun N j => (P N).stage j) hfinite
    (fun N => (genuineCohomologyColimits_standard i n (K N)).1)
    (fun N k => (genuineCohomologyColimits_standard i n (K N)).2 k)
    hzero htest M q

end StandardExt

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
