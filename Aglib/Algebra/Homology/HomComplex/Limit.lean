/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.HomComplex.Colimit

/-!
# Native Hom complexes send source colimits to inverse limits

This constructs the actual limit cone for the whole source diagram. Restricting
the source diagram to all strict predecessors therefore gives the complete
predecessor limit needed by the ordinal primitive argument.
-/

@[expose] public noncomputable section

universe w w' v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]
  (F : J ⥤ CochainComplex C ℤ) (I : CochainComplex C ℤ)

/-- The actual inverse diagram obtained by precomposition. -/
def inverseDiagram : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℤ where
  obj j := HomComplex (F.obj j.unop) I
  map f := precompMap (F.map f.unop) I
  map_id j := by simp
  map_comp f g := by simp [precompMap_comp]

/-- The canonical cone from the Hom complex of the original source colimit. -/
def colimitCone : Cone (inverseDiagram F I) where
  pt := HomComplex (colimit F) I
  π :=
    { app := fun j => precompMap (colimit.ι F j.unop) I
      naturality := fun j k f => by
        dsimp [inverseDiagram]
        rw [Category.id_comp, ← precompMap_comp, colimit.w] }

/-- A cone component, explicitly typed as the original native cochain. -/
def coneCochain (s : Cone (inverseDiagram F I)) (n : ℤ) (x : s.pt.X n) (j : J) :
    Cochain (F.obj j) I n := (s.π.app (op j)).f n x

omit [HasColimitsOfShape J C] in
/-- Components of an arbitrary native inverse-system cone are compatible cochains. -/
lemma cone_compatible (s : Cone (inverseDiagram F I)) (n : ℤ) (x : s.pt.X n)
    {j k : J} (f : j ⟶ k) :
    (Cochain.ofHom (F.map f)).comp ((s.π.app (op k)).f n x) (zero_add n) =
      (s.π.app (op j)).f n x := by
  have h := congrArg (fun a => a.f n x) (s.w f.op)
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Lift an arbitrary cone using the actual componentwise colimit property. -/
def colimitConeLift (s : Cone (inverseDiagram F I)) : s.pt ⟶ (colimitCone F I).pt where
  f n := AddCommGrpCat.ofHom
    { toFun := fun x => cochainDesc F I n (coneCochain F I s n x)
        (cone_compatible F I s n x)
      map_zero' := by
        apply cochain_ext_colimit F I n
        intro j
        rw [cochainDesc_precomp, Cochain.comp_zero]
        exact map_zero ((s.π.app (op j)).f n).hom
      map_add' := fun x y => by
        apply cochain_ext_colimit F I n
        intro j
        rw [Cochain.comp_add, cochainDesc_precomp, cochainDesc_precomp, cochainDesc_precomp]
        exact map_add ((s.π.app (op j)).f n).hom x y }
  comm' n m _hnm := by
    ext x
    change δ n m (cochainDesc F I n (coneCochain F I s n x)
      (cone_compatible F I s n x)) =
      cochainDesc F I m (coneCochain F I s m (s.pt.d n m x))
        (cone_compatible F I s m (s.pt.d n m x))
    apply cochain_ext_colimit F I m
    intro j
    rw [← δ_ofHom_comp, cochainDesc_precomp, cochainDesc_precomp]
    exact congrArg (fun a => a x) ((s.π.app (op j)).comm n m)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma colimitConeLift_π (s : Cone (inverseDiagram F I)) (j : Jᵒᵖ) :
    colimitConeLift F I s ≫ (colimitCone F I).π.app j = s.π.app j := by
  ext n x
  exact cochainDesc_precomp F I n (coneCochain F I s n x)
    (cone_compatible F I s n x) j.unop

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Hom-complex cone is genuinely limiting. -/
def colimitConeIsLimit : IsLimit (colimitCone F I) where
  lift := colimitConeLift F I
  fac := colimitConeLift_π F I
  uniq s m hm := by
    ext n x
    change (m.f n x : Cochain (colimit F) I n) =
      cochainDesc F I n (coneCochain F I s n x) (cone_compatible F I s n x)
    apply cochain_ext_colimit F I n
    intro j
    rw [cochainDesc_precomp]
    exact congrArg (fun a => a.f n x) (hm (op j))

end CochainComplex.HomComplex
