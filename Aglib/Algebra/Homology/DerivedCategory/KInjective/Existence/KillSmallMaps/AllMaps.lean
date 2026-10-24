/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.KillSmallMaps.QuasiIso
public import Mathlib.Algebra.Homology.GrothendieckAbelian

/-!
# Simultaneously killing all maps from a small family

Local smallness in the actual Grothendieck universe bounds the indexing type
of all original maps. The family itself remains an explicit input; this does
not assert the missing existence or detection property of a small acyclic test set.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ) (K : CochainComplex C ℤ)

/-- The actual small indexing type of every map from the prescribed family. -/
abbrev killAllMapsIndex := Σ i, Shrink.{w} (A i ⟶ K)

/-- The original sources, repeated once for every original map. -/
abbrev killAllMapsSources (s : killAllMapsIndex A K) : CochainComplex C ℤ := A s.1

/-- Recover the original map from its small-universe index. -/
def killAllMapsEvaluation (s : killAllMapsIndex A K) : killAllMapsSources A K s ⟶ K :=
  (equivShrink (A s.1 ⟶ K)).symm s.2

/-- The actual native attachment for all maps from the prescribed family. -/
abbrev killAllMapsAttachment : CochainComplex C ℤ :=
  killSmallMapsAttachment (killAllMapsSources A K) (killAllMapsEvaluation A K)

/-- The original inclusion into the all-maps attachment. -/
abbrev killAllMapsι : K ⟶ killAllMapsAttachment A K :=
  killSmallMapsι (killAllMapsSources A K) (killAllMapsEvaluation A K)

instance killAllMapsι_mono : Mono (killAllMapsι A K) := inferInstance

/-- Every actual map from the family has a specified nullhomotopy after inclusion. -/
def killAllMapsHomotopy (i : ι) (f : A i ⟶ K) :
    Homotopy (f ≫ killAllMapsι A K) 0 := by
  simpa [killAllMapsEvaluation] using
    killSmallMapsHomotopy (killAllMapsSources A K) (killAllMapsEvaluation A K)
      ⟨i, equivShrink (A i ⟶ K) f⟩

/-- The original all-maps inclusion is a quasi-isomorphism for an acyclic family. -/
lemma killAllMapsι_quasiIso (hA : ∀ i, (A i).Acyclic) : QuasiIso (killAllMapsι A K) :=
  killSmallMapsι_quasiIso (killAllMapsSources A K) (killAllMapsEvaluation A K)
    (fun s => hA s.1)

end CochainComplex
