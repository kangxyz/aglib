/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Uniqueness
public import Aglib.AlgebraicGeometry.Compactification.BaseChange

/-!
# Source-isomorphism transport of dense compactifications

Reuse the supplied compactification transport. The ambient scheme, proper map,
and refinement maps remain unchanged; the original open map is precomposed
with the specified source isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X X' S : Scheme.{u}} {f : X ⟶ S} (f' : X' ⟶ S)
  (e : X' ≅ X) (h : e.hom ≫ f = f')

/-- Transport the supplied dense compactification along its actual source isomorphism. -/
def ofSourceIso (C : DenseCompactification f) : DenseCompactification f' where
  toCompactification := C.toCompactification.ofSourceIso f' e h
  isSchemeTheoreticallyDominant_j :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (e.hom ≫ C.j))

/-- Source transport preserves the actual ambient refinement morphisms. -/
def sourceIso : DenseCompactification f ⥤ DenseCompactification f' where
  obj := ofSourceIso f' e h
  map {C D} a :=
    { hom := a.hom
      isProper_hom := a.isProper_hom
      open_fac := by
        change (e.hom ≫ C.j) ≫ a.hom = e.hom ≫ D.j
        exact (Category.assoc _ _ _).trans (congrArg (fun k => e.hom ≫ k) a.open_fac)
      base_fac := a.base_fac }
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma sourceIso_obj_j (C : DenseCompactification f) :
    ((sourceIso f' e h).obj C).j = e.hom ≫ C.j := rfl

@[simp]
lemma sourceIso_obj_p (C : DenseCompactification f) :
    ((sourceIso f' e h).obj C).p = C.p := rfl

@[simp]
lemma sourceIso_map_hom {C D : DenseCompactification f} (a : C ⟶ D) :
    ((sourceIso f' e h).map a).hom = a.hom := rfl

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
