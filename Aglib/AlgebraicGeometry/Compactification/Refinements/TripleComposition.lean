/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Composition

/-! # Actual three-level compactification towers

The data are three dense compactifications, with existence supplied by Nagata.
No associativity, comparison, or compatibility equation is assumed as data.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)

/-- Three actual proper ambients, retaining all three original open embeddings. -/
structure TripleCompactifiedComposition where
  /-- Compactify the final map first. -/
  last : DenseCompactification h
  /-- Compactify the middle source over that ambient. -/
  middle : DenseCompactification (g ≫ last.j)
  /-- Compactify the original source over the middle ambient. -/
  first : DenseCompactification (f ≫ middle.j)

namespace TripleCompactifiedComposition
variable {f g h} (T : TripleCompactifiedComposition f g h)

/-- The final two maps form the literal supplied binary tower. -/
def tail : CompactifiedComposition g h := ⟨T.last, T.middle⟩

/-- The right-associated outer tower retains the first compactification. -/
def rightOuter : CompactifiedComposition f (g ≫ h) := ⟨T.tail.composite, T.first⟩

/-- The left-associated outer tower composes the two original proper maps. -/
def leftOuter : CompactifiedComposition (f ≫ g) h where
  targetCompactification := T.last
  sourceCompactification :=
    { Xbar := T.first.Xbar
      j := T.first.j
      p := T.first.p ≫ T.middle.p
      isOpenImmersion_j := inferInstance
      isProper_p := inferInstance
      fac := by
        rw [← Category.assoc, T.first.fac, Category.assoc, T.middle.fac,
          ← Category.assoc]
      isSchemeTheoreticallyDominant_j := inferInstance }

end TripleCompactifiedComposition

/-- Existing Nagata existence constructs the three levels; compatibility is not assumed. -/
instance tripleCompactifiedComposition_nonempty
    [CompactSpace W] [QuasiSeparatedSpace W]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    Nonempty (TripleCompactifiedComposition f g h) := by
  obtain ⟨C⟩ := (inferInstance : Nonempty (CompactifiedComposition g h))
  let : CompactSpace C.targetCompactification.Xbar :=
    QuasiCompact.compactSpace_of_compactSpace C.targetCompactification.p
  let : QuasiSeparatedSpace C.targetCompactification.Xbar :=
    quasiSeparatedSpace_of_quasiSeparated C.targetCompactification.p
  let : CompactSpace C.sourceCompactification.Xbar :=
    QuasiCompact.compactSpace_of_compactSpace C.sourceCompactification.p
  let : QuasiSeparatedSpace C.sourceCompactification.Xbar :=
    quasiSeparatedSpace_of_quasiSeparated C.sourceCompactification.p
  obtain ⟨D⟩ := (inferInstance :
    Nonempty (DenseCompactification (f ≫ C.sourceCompactification.j)))
  exact ⟨⟨C.targetCompactification, C.sourceCompactification, D⟩⟩

end AlgebraicGeometry.Scheme.Hom
