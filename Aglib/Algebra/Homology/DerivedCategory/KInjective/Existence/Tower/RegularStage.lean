/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.Stages
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.Cardinal
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.InjectiveColimit
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Tower.TestColimit

/-!
# The actual regular stage is termwise injective and kills the tests

A single constructed regular ordinal works for every input complex. The two
final properties follow from native stage factorization and the original
successor maps, not from any assumed replacement predicate.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ) (G : C)

/-- The actual functor obtained at the constructed uniform regular ordinal. -/
abbrev regularReplacementFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  replacementIteration A (replacementIndex A G)

/-- The original natural augmentation into that actual regular stage. -/
abbrev regularReplacementUnit : 𝟭 (CochainComplex C ℤ) ⟶ regularReplacementFunctor A G :=
  replacementIterationUnit A (replacementIndex A G)

instance regularReplacementUnit_mono (K : CochainComplex C ℤ) :
    Mono ((regularReplacementUnit A G).app K) := inferInstance

variable (hG : IsSeparator G) (K : CochainComplex C ℤ)

include hG in
/-- Every actual term of the regular stage is injective. -/
lemma regularReplacement_injective (n : ℤ) :
    Injective (((regularReplacementFunctor A G).obj K).X n) := by
  let J := replacementIndex A G
  let F := replacementTowerAt A J K ⋙ eval C (.up ℤ) n
  have (i j : J) (f : i ⟶ j) : Mono (F.map f) := by
    dsimp [F]
    infer_instance
  exact CategoryTheory.IsGrothendieckAbelian.injective_of_colimit_injective_factors hG F
    (isColimitOfPreserves (eval C (.up ℤ) n) (replacementTowerAtIsColimit A J K))
    (replacementCardinal_separator A G)
    (fun j => replacementTowerCocone_injectiveFactor A J K j (not_isMax j) n)

/-- Every actual test map into the final regular stage is nullhomotopic. -/
lemma regularReplacement_test_nullhomotopic (i : ι)
    (z : A i ⟶ (regularReplacementFunctor A G).obj K) : Nonempty (Homotopy z 0) := by
  let J := replacementIndex A G
  apply nonempty_homotopy_zero_of_colimit_stage (replacementTowerAt A J K)
    (replacementTowerAtIsColimit A J K) (A i) (replacementCardinal_test A G i) ?_ z
  intro j f
  exact ⟨Order.succ j, homOfLE (Order.le_succ j),
    ⟨replacementTowerStageHomotopy A J K j (not_isMax j) i f⟩⟩

end CochainComplex
