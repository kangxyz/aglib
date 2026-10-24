/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Quasi-isomorphisms and exact colimits of complexes

A diagram of native complexes gives a complex of evaluated functors. Applying
exact colimits to that complex preserves quasi-isomorphisms. The canonical
comparison with the native colimit retains the original colimit injections
and the original map induced by a natural transformation.
-/

@[expose] public noncomputable section

universe w w' t v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J]
  {ι : Type t} {c : ComplexShape ι}

section

variable [HasZeroMorphisms C]

/-- A diagram of native complexes, read degreewise as a complex of functors. -/
def diagramComplex (F : J ⥤ HomologicalComplex C c) : HomologicalComplex (J ⥤ C) c where
  X n := F ⋙ eval C c n
  d n m :=
    { app j := (F.obj j).d n m
      naturality i j f := (F.map f).comm n m }
  shape n m h := by
    ext j
    exact (F.obj j).shape n m h
  d_comp_d' n m k _ _ := by
    ext j
    exact (F.obj j).d_comp_d n m k

/-- The original components of a natural transformation give a chain map. -/
def diagramComplexMap {F G : J ⥤ HomologicalComplex C c} (α : F ⟶ G) :
    diagramComplex F ⟶ diagramComplex G where
  f n := Functor.whiskerRight α (eval C c n)
  comm' n m _ := by
    ext j
    exact (α.app j).comm n m

end

variable [Abelian C] [HasColimitsOfShape J C]

set_option backward.isDefEq.respectTransparency false in
/-- The native colimit compared with the degreewise colimit complex. -/
def diagramComplexColimitIso (F : J ⥤ HomologicalComplex C c) :
    colimit F ≅ ((colim (J := J) (C := C)).mapHomologicalComplex c).obj
      (diagramComplex F) :=
  (colimit.isColimit F).coconePointUniqueUpToIso (isColimitCoconeOfHasColimitEval F)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_diagramComplexColimitIso_hom (F : J ⥤ HomologicalComplex C c) (j : J) :
    colimit.ι F j ≫ (diagramComplexColimitIso F).hom =
      (coconeOfHasColimitEval F).ι.app j :=
  colimit.comp_coconePointUniqueUpToIso_hom _ j

set_option backward.isDefEq.respectTransparency false in
/-- Naturality for the original map between the native colimits. -/
@[reassoc]
lemma diagramComplexColimitIso_naturality {F G : J ⥤ HomologicalComplex C c} (α : F ⟶ G) :
    colim.map α ≫ (diagramComplexColimitIso G).hom =
      (diagramComplexColimitIso F).hom ≫
        ((colim (J := J) (C := C)).mapHomologicalComplex c).map (diagramComplexMap α) := by
  apply colimit.hom_ext
  intro j
  simp only [colimit.ι_map_assoc, ι_diagramComplexColimitIso_hom,
    ι_diagramComplexColimitIso_hom_assoc]
  ext n
  change (α.app j).f n ≫ colimit.ι (G ⋙ eval C c n) j =
    colimit.ι (F ⋙ eval C c n) j ≫ colim.map (Functor.whiskerRight α (eval C c n))
  exact (colimit.ι_map (Functor.whiskerRight α (eval C c n)) j).symm

variable [HasExactColimitsOfShape J C]

set_option backward.isDefEq.respectTransparency false in
/-- Exact colimits preserve pointwise quasi-isomorphisms of native complexes. -/
lemma quasiIso_colimMap {F G : J ⥤ HomologicalComplex C c} (α : F ⟶ G)
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (colim.map α) := by
  let : (colim (J := J) (C := C)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : QuasiIso (diagramComplexMap α) :=
    (quasiIso_iff_evaluation _).2 (fun j => by
      change QuasiIso (α.app j)
      exact hα j)
  have : QuasiIso (((colim (J := J) (C := C)).mapHomologicalComplex c).map
      (diagramComplexMap α)) :=
    quasiIso_map_of_preservesHomology (diagramComplexMap α) (colim (J := J) (C := C))
  have : QuasiIso (colim.map α ≫ (diagramComplexColimitIso G).hom) := by
    rw [diagramComplexColimitIso_naturality]
    infer_instance
  exact quasiIso_of_comp_right (colim.map α) (diagramComplexColimitIso G).hom

end HomologicalComplex
