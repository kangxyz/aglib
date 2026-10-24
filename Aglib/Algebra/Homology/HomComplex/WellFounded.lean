/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.HomComplex.Continuity
public import Aglib.Algebra.Homology.HomComplex.EvaluatedLimit
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.Acyclic

/-!
# The entire-predecessor inverse-limit theorem for native Hom complexes

The source comparison is the map from the colimit of all strict predecessors.
Its monicity, not merely monicity of individual transitions, supplies the
surjectivity used by the actual compatible-primitive recurrence.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [PartialOrder J]
  (F : J ⥤ CochainComplex C ℤ) (I : CochainComplex C ℤ)
  [∀ i : J, HasColimitsOfShape (Set.Iio i) C]

instance hasLimit_homPredecessors (i : J) :
    HasLimit (InverseLimit.predecessors (inverseDiagram F I) i) :=
  inferInstanceAs (HasLimit (inverseDiagram (InverseLimit.predecessorInclusion i ⋙ F) I))

instance hasLimit_evaluatedHomPredecessors (i : J) (n : ℤ) :
    HasLimit (InverseLimit.predecessors (inverseDiagram F I) i ⋙
      HomologicalComplex.eval AddCommGrpCat (.up ℤ) n) :=
  inferInstanceAs (HasLimit (inverseDiagram (InverseLimit.predecessorInclusion i ⋙ F) I ⋙
    HomologicalComplex.eval AddCommGrpCat (.up ℤ) n))

/-- The actual source cocone on all strict predecessors. -/
def sourcePredecessorCocone (i : J) :
    Cocone (InverseLimit.predecessorInclusion i ⋙ F) where
  pt := F.obj i
  ι :=
    { app := fun j => F.map (homOfLE j.property.le)
      naturality := fun j k f => by
        dsimp [InverseLimit.predecessorInclusion]
        rw [Category.comp_id, ← F.map_comp]
        congr 1 }

/-- The original source map from the colimit of the full initial segment. -/
def sourcePredecessorComparison (i : J) :
    colimit (InverseLimit.predecessorInclusion i ⋙ F) ⟶ F.obj i :=
  colimit.desc _ (sourcePredecessorCocone F i)

set_option backward.isDefEq.respectTransparency false in
/-- The full-limit comparison is exactly the native Hom comparison, with its
original augmentation and projections retained. -/
lemma predecessorComparison_eq (i : J) :
    InverseLimit.predecessorComparison (inverseDiagram F I) i =
      limitComparison (InverseLimit.predecessorInclusion i ⋙ F) I
        (sourcePredecessorComparison F i) := by
  apply limit.hom_ext
  intro j
  rw [InverseLimit.predecessorComparison_π]
  have hp : (colimitIsoLimit (InverseLimit.predecessorInclusion i ⋙ F) I).hom ≫
      limit.π (InverseLimit.predecessors (inverseDiagram F I) i) j =
      precompMap (colimit.ι (InverseLimit.predecessorInclusion i ⋙ F) j.unop) I :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (colimitConeIsLimit (InverseLimit.predecessorInclusion i ⋙ F) I)
      (limit.isLimit _) j
  dsimp only [limitComparison]
  rw [Category.assoc, hp]
  change precompMap (F.map (homOfLE j.unop.property.le)) I =
    precompMap (sourcePredecessorComparison F i) I ≫
      precompMap (colimit.ι (InverseLimit.predecessorInclusion i ⋙ F) j.unop) I
  rw [← precompMap_comp]
  congr 1
  exact (colimit.ι_desc (sourcePredecessorCocone F i) j.unop).symm

/-- Monicity of the entire source predecessor comparison gives the exact
surjectivity required by the inverse-limit theorem. -/
lemma predecessorComparison_surjective (i : J)
    [Mono (sourcePredecessorComparison F i)] [∀ n, Injective (I.X n)] (n : ℤ) :
    Function.Surjective ((InverseLimit.predecessorComparison (inverseDiagram F I) i).f n) := by
  rw [predecessorComparison_eq]
  exact limitComparison_surjective _ I _ n

variable [HasColimitsOfShape J C]

/-- Acyclic stage Hom complexes remain acyclic at the entire source colimit,
using the actual well-founded primitive recursion. -/
lemma acyclic_colimit_of_wellFounded
    (hr : WellFounded ((· < ·) : J → J → Prop))
    [∀ i, Mono (sourcePredecessorComparison F i)] [∀ n, Injective (I.X n)]
    (hF : ∀ i, (HomComplex (F.obj i) I).Acyclic) :
    (HomComplex (colimit F) I).Acyclic := by
  have h := InverseLimit.acyclic_limit_of_surjective_predecessorComparison hr
    (inverseDiagram F I) hF (fun i n => predecessorComparison_surjective F I i n)
  intro n
  exact (h n).of_iso (colimitIsoLimit F I).symm

end CochainComplex.HomComplex
