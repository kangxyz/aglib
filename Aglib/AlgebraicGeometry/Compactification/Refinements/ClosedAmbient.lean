/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Uniqueness

/-!
# Comparing dense compactifications in a common closed ambient scheme

The maps are constructed by the existing closed-target lifting theorem.
No commutation of schematic image with arbitrary base change is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S P : Scheme.{u}} {f : X ⟶ S} (C D : DenseCompactification f)
  (p : P ⟶ S) (i : C.Xbar ⟶ P) (k : D.Xbar ⟶ P) [IsClosedImmersion k]
  (hj : C.j ≫ i = D.j ≫ k) (hi : i ≫ p = C.p) (hk : k ≫ p = D.p)

/-- The actual lift through the closed ambient embedding of the target. -/
def closedAmbientMap : C.Xbar ⟶ D.Xbar :=
  Scheme.QuasiDomination.closedTargetLift C.j k i D.j hj

@[reassoc (attr := simp)]
lemma closedAmbientMap_comp : closedAmbientMap C D i k hj ≫ k = i :=
  Scheme.QuasiDomination.closedTargetLift_comp _ _ _ _ _

@[reassoc (attr := simp)]
lemma j_closedAmbientMap : C.j ≫ closedAmbientMap C D i k hj = D.j :=
  Scheme.QuasiDomination.comp_closedTargetLift _ _ _ _ _

include hi hk in
/-- The closed-target lift retains the original structural map. -/
@[reassoc]
lemma closedAmbientMap_p : closedAmbientMap C D i k hj ≫ D.p = C.p := by
  calc
    _ = closedAmbientMap C D i k hj ≫ (k ≫ p) :=
      congrArg (fun a => closedAmbientMap C D i k hj ≫ a) hk.symm
    _ = (closedAmbientMap C D i k hj ≫ k) ≫ p := (Category.assoc _ _ _).symm
    _ = i ≫ p := congrArg (fun a => a ≫ p) (closedAmbientMap_comp C D i k hj)
    _ = C.p := hi

/-- A closed target in a common ambient yields an actual proper refinement. -/
def closedAmbientRefinement : C ⟶ D where
  hom := closedAmbientMap C D i k hj
  isProper_hom := by
    have hComposite : IsProper (closedAmbientMap C D i k hj ≫ D.p) := by
      rw [closedAmbientMap_p C D p i k hj hi hk]
      infer_instance
    exact @IsProper.of_comp _ _ _ (closedAmbientMap C D i k hj) D.p hComposite
      (inferInstanceAs (IsSeparated D.p))
  open_fac := j_closedAmbientMap C D i k hj
  base_fac := closedAmbientMap_p C D p i k hj hi hk

/-- Two dense closed compactifications with the same original open map are
canonically isomorphic by actual refinements in both directions. -/
def closedAmbientIso [IsClosedImmersion i] : C ≅ D where
  hom := closedAmbientRefinement C D p i k hj hi hk
  inv := closedAmbientRefinement D C p k i hj.symm hk hi
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The comparison is normalized by its original ambient inclusion equation. -/
@[reassoc (attr := simp)]
lemma closedAmbientIso_hom_comp [IsClosedImmersion i] :
    (closedAmbientIso C D p i k hj hi hk).hom.hom ≫ k = i :=
  closedAmbientMap_comp C D i k hj

/-- The inverse comparison has the corresponding original inclusion equation. -/
@[reassoc (attr := simp)]
lemma closedAmbientIso_inv_comp [IsClosedImmersion i] :
    (closedAmbientIso C D p i k hj hi hk).inv.hom ≫ i = k :=
  closedAmbientMap_comp D C k i hj.symm

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
