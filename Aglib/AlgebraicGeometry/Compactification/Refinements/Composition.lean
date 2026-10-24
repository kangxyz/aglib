/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenRestriction
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Cofiltered

/-!
# Actual compactified composition towers

First compactify the second map, then compactify the source over that ambient
scheme. The intermediate compactification is the literal inverse image of the
original middle scheme. Nagata supplies the two objects; no comparison or
common-refinement existence field is added to the tower.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Two actual compactifications forming a compactified composition tower. -/
structure CompactifiedComposition where
  /-- The compactification of the middle scheme over the final base. -/
  targetCompactification : DenseCompactification g
  /-- The compactification of the source over the compactified middle scheme. -/
  sourceCompactification : DenseCompactification (f ≫ targetCompactification.j)

namespace CompactifiedComposition

variable {f g} (C : CompactifiedComposition f g)

/-- The original source embedded in a proper scheme over the final base. -/
def composite : DenseCompactification (f ≫ g) where
  Xbar := C.sourceCompactification.Xbar
  j := C.sourceCompactification.j
  p := C.sourceCompactification.p ≫ C.targetCompactification.p
  isOpenImmersion_j := inferInstance
  isProper_p := inferInstance
  fac := by
    rw [← Category.assoc, C.sourceCompactification.fac, Category.assoc,
      C.targetCompactification.fac]
  isSchemeTheoreticallyDominant_j := inferInstance

variable [QuasiCompact g]

/-- The compactification of the first map obtained from the literal open pullback. -/
def first : DenseCompactification f :=
  DenseCompactification.openRestriction f C.targetCompactification.j C.sourceCompactification

/-- The intermediate open immersion is the second projection of the literal pullback. -/
def middleOpen : (first C).Xbar ⟶ C.sourceCompactification.Xbar :=
  pullback.snd C.targetCompactification.j C.sourceCompactification.p

instance middleOpen_isOpenImmersion : IsOpenImmersion (middleOpen C) :=
  inferInstanceAs
    (IsOpenImmersion (pullback.snd C.targetCompactification.j C.sourceCompactification.p))

/-- The tower retains the original open embedding of the source into the ambient scheme. -/
@[reassoc (attr := simp)]
lemma first_j_middleOpen : (first C).j ≫ middleOpen C = C.sourceCompactification.j :=
  DenseCompactification.openRestriction_j_snd _ _ _

/-- The proper/open square of the tower is the actual pullback square. -/
lemma isPullback_middleOpen :
    IsPullback (middleOpen C) (first C).p C.sourceCompactification.p
      C.targetCompactification.j :=
  DenseCompactification.isPullback_openRestriction _ _ _

end CompactifiedComposition

/-- The supplied Nagata theorem constructs both actual compactifications in a
composition tower over a qcqs final base. -/
instance compactifiedComposition_nonempty [CompactSpace Z] [QuasiSeparatedSpace Z]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    Nonempty (CompactifiedComposition f g) := by
  obtain ⟨C⟩ := (inferInstance : Nonempty (DenseCompactification g))
  let : CompactSpace C.Xbar := QuasiCompact.compactSpace_of_compactSpace C.p
  let : QuasiSeparatedSpace C.Xbar := quasiSeparatedSpace_of_quasiSeparated C.p
  obtain ⟨D⟩ := (inferInstance : Nonempty (DenseCompactification (f ≫ C.j)))
  exact ⟨⟨C, D⟩⟩

end AlgebraicGeometry.Scheme.Hom
