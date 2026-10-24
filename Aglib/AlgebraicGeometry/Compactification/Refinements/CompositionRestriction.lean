/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionRefinement

/-!
# Restricting actual refinements of compactified composition towers

A compatible proper refinement of towers induces an actual proper refinement of
the intermediate compactifications. Its map is the literal pullback lift, and
its equation with the intermediate open immersions is retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.CompactifiedComposition.Refinement

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} [QuasiCompact g]
  {C D : CompactifiedComposition f g} (a : Refinement C D)

/-- The map on intermediate ambients is the original pullback lift. -/
def intermediateMap : (first C).Xbar ⟶ (first D).Xbar :=
  pullback.lift (first C).p (middleOpen C ≫ a.source.hom) (by
    calc
      _ = (first C).p ≫ (C.targetCompactification.j ≫ a.target.hom) :=
        congrArg (fun k => (first C).p ≫ k) a.target.open_fac.symm
      _ = ((first C).p ≫ C.targetCompactification.j) ≫ a.target.hom :=
        (Category.assoc _ _ _).symm
      _ = (middleOpen C ≫ C.sourceCompactification.p) ≫ a.target.hom :=
        congrArg (fun k => k ≫ a.target.hom)
          (show (first C).p ≫ C.targetCompactification.j =
            middleOpen C ≫ C.sourceCompactification.p from pullback.condition)
      _ = middleOpen C ≫ (C.sourceCompactification.p ≫ a.target.hom) :=
        Category.assoc _ _ _
      _ = middleOpen C ≫ (a.source.hom ≫ D.sourceCompactification.p) :=
        congrArg (fun k => middleOpen C ≫ k) a.comm.symm
      _ = _ := (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
lemma intermediateMap_p : intermediateMap a ≫ (first D).p = (first C).p :=
  pullback.lift_fst _ _ _

/-- The refinement preserves the actual intermediate open maps. -/
@[reassoc (attr := simp)]
lemma intermediateMap_middleOpen :
    intermediateMap a ≫ middleOpen D = middleOpen C ≫ a.source.hom :=
  pullback.lift_snd _ _ _

/-- The original source embedding is preserved by the induced intermediate map. -/
@[reassoc (attr := simp)]
lemma first_j_intermediateMap : (first C).j ≫ intermediateMap a = (first D).j := by
  apply pullback.hom_ext
  · change ((first C).j ≫ intermediateMap a) ≫ (first D).p =
      (first D).j ≫ (first D).p
    rw [Category.assoc, intermediateMap_p, (first C).fac, (first D).fac]
  · change ((first C).j ≫ intermediateMap a) ≫ middleOpen D =
      (first D).j ≫ middleOpen D
    let h : C.sourceCompactification.Xbar ⟶ D.sourceCompactification.Xbar := a.source.hom
    calc
      _ = (first C).j ≫ (middleOpen C ≫ h) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => (first C).j ≫ k) (intermediateMap_middleOpen a))
      _ = ((first C).j ≫ middleOpen C) ≫ h := (Category.assoc _ _ _).symm
      _ = C.sourceCompactification.j ≫ h :=
        congrArg (fun k => k ≫ h) (first_j_middleOpen C)
      _ = D.sourceCompactification.j := a.source.open_fac
      _ = _ := (first_j_middleOpen D).symm

instance intermediateMap_isProper : IsProper (intermediateMap a) := by
  have : IsProper (intermediateMap a ≫ (first D).p) := by
    rw [intermediateMap_p]
    infer_instance
  exact IsProper.of_comp (intermediateMap a) (first D).p

/-- The induced refinement of the actual compactifications of the first map. -/
def intermediate : first C ⟶ first D where
  hom := intermediateMap a
  isProper_hom := inferInstance
  open_fac := first_j_intermediateMap a
  base_fac := intermediateMap_p a

end AlgebraicGeometry.Scheme.Hom.CompactifiedComposition.Refinement
