/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange

/-! # Original raw pullback geometry for exceptional exchange coherence -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme.Hom.Compactification

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  (C D : Compactification f) (h : C.Xbar ⟶ D.Xbar) (hp : h ≫ D.p = C.p) (b : T ⟶ S)

/-- The actual ambient pullback of a specified raw refinement. -/
def refinementBaseChangeMap : pullback b C.p ⟶ pullback b D.p :=
  pullback.lift (pullback.fst b C.p) (pullback.snd b C.p ≫ h) (by
    rw [Category.assoc, hp]
    exact pullback.condition)

/-- The actual raw-refinement pullback map preserves its base projection. -/
@[reassoc (attr := simp)]
theorem refinementBaseChangeMap_fst :
    refinementBaseChangeMap C D h hp b ≫ pullback.fst b D.p = pullback.fst b C.p :=
  pullback.lift_fst _ _ _

/-- The second projection retains exactly the original ambient refinement. -/
@[reassoc (attr := simp)]
theorem refinementBaseChangeMap_snd :
    refinementBaseChangeMap C D h hp b ≫ pullback.snd b D.p = pullback.snd b C.p ≫ h :=
  pullback.lift_snd _ _ _

/-- The actual ambient lift is Cartesian over the original raw refinement. -/
theorem isPullback_refinementBaseChangeMap :
    IsPullback (pullback.snd b C.p) (refinementBaseChangeMap C D h hp b) h
      (pullback.snd b D.p) := by
  have hout : IsPullback
      (refinementBaseChangeMap C D h hp b ≫ pullback.fst b D.p)
      (pullback.snd b C.p) b (h ≫ D.p) := by
    simpa only [refinementBaseChangeMap_fst, hp] using
      (IsPullback.of_hasPullback b C.p)
  exact (hout.of_right (refinementBaseChangeMap_snd C D h hp b)
    (IsPullback.of_hasPullback b D.p)).flip

variable (sq : IsPullback C.j (𝟙 X) h D.j)

include sq in
/-- The original Cartesian open comparison is preserved by the literal lift. -/
@[reassoc (attr := simp)]
theorem baseChange_j_refinementMap :
    (C.baseChange b).j ≫ refinementBaseChangeMap C D h hp b = (D.baseChange b).j := by
  let jC : pullback b f ⟶ pullback b C.p := (C.baseChange b).j
  let jD : pullback b f ⟶ pullback b D.p := (D.baseChange b).j
  change jC ≫ refinementBaseChangeMap C D h hp b = jD
  have ho : C.j ≫ h = D.j := sq.w.trans (Category.id_comp _)
  have hjC : jC ≫ pullback.snd b C.p = pullback.snd b f ≫ C.j :=
    baseChange_j_snd C b
  apply pullback.hom_ext
  · calc
      (jC ≫ refinementBaseChangeMap C D h hp b) ≫ pullback.fst b D.p =
          jC ≫ pullback.fst b C.p := by
            rw [Category.assoc, refinementBaseChangeMap_fst]
      _ = pullback.fst b f := baseChange_j_fst C b
      _ = jD ≫ pullback.fst b D.p := (baseChange_j_fst D b).symm
  · calc
      (jC ≫ refinementBaseChangeMap C D h hp b) ≫ pullback.snd b D.p =
          jC ≫ (pullback.snd b C.p ≫ h) := by
            rw [Category.assoc, refinementBaseChangeMap_snd]
      _ = (pullback.snd b f ≫ C.j) ≫ h := by
        rw [← Category.assoc, hjC]
      _ = pullback.snd b f ≫ D.j := by rw [Category.assoc, ho]
      _ = jD ≫ pullback.snd b D.p := (baseChange_j_snd D b).symm

include sq in
/-- Raw refinement base change preserves the actual common-open pullback
square without requiring either raw ambient scheme to be dense. -/
theorem isPullback_refinementBaseChangeMap_open :
    IsPullback (C.baseChange b).j (𝟙 (pullback b f))
      (refinementBaseChangeMap C D h hp b) (D.baseChange b).j := by
  let jC : pullback b f ⟶ pullback b C.p := (C.baseChange b).j
  let jD : pullback b f ⟶ pullback b D.p := (D.baseChange b).j
  change IsPullback jC (𝟙 (pullback b f)) (refinementBaseChangeMap C D h hp b) jD
  have hC : IsPullback (pullback.snd b f) jC C.j (pullback.snd b C.p) :=
    EtaleCohomology.isPullback_rawCompactificationOpen C b
  have hD : IsPullback (pullback.snd b f) jD D.j (pullback.snd b D.p) :=
    EtaleCohomology.isPullback_rawCompactificationOpen D b
  have hopen : jC ≫ refinementBaseChangeMap C D h hp b = jD :=
    baseChange_j_refinementMap C D h hp b sq
  have hout : IsPullback (𝟙 (pullback b f) ≫ pullback.snd b f) jC D.j
      (refinementBaseChangeMap C D h hp b ≫ pullback.snd b D.p) := by
    rw [refinementBaseChangeMap_snd C D h hp b]
    simpa only [Category.id_comp, Category.comp_id] using (hC.paste_horiz sq.flip)
  exact (hout.of_right ((Category.id_comp _).trans hopen.symm) hD).flip

end AlgebraicGeometry.Scheme.Hom.Compactification
