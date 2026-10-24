/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.HomComplex.Limit

/-!
# Actual evaluated Hom-complex limits with independent universes

Source colimits supply these particular limits of abelian groups even when the
source indexing universe is not bounded by the morphism universe. No assumption
of arbitrary limits of that shape in `AddCommGrpCat` is made.
-/

@[expose] public noncomputable section

universe w w' v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]
  (F : J ⥤ CochainComplex C ℤ) (I : CochainComplex C ℤ) (n : ℤ)

omit [HasColimitsOfShape J C] in
/-- Elements of an arbitrary evaluated cone are actual compatible cochains. -/
lemma evaluatedCone_compatible
    (s : Cone (inverseDiagram F I ⋙ eval AddCommGrpCat (.up ℤ) n)) (x : s.pt)
    {j k : J} (f : j ⟶ k) :
    (Cochain.ofHom (F.map f)).comp (s.π.app (op k) x) (zero_add n) =
      s.π.app (op j) x := by
  exact congrArg (fun a => a x) (s.w f.op)

set_option backward.isDefEq.respectTransparency false in
/-- Lift an arbitrary evaluated cone by the original cochain colimit descent. -/
def evaluatedColimitConeLift
    (s : Cone (inverseDiagram F I ⋙ eval AddCommGrpCat (.up ℤ) n)) :
    s.pt ⟶ (HomComplex (colimit F) I).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun x => cochainDesc F I n (fun j => s.π.app (op j) x)
        (evaluatedCone_compatible F I n s x)
      map_zero' := by
        apply cochain_ext_colimit F I n
        intro j
        rw [cochainDesc_precomp, Cochain.comp_zero]
        exact map_zero (s.π.app (op j)).hom
      map_add' := fun x y => by
        apply cochain_ext_colimit F I n
        intro j
        rw [Cochain.comp_add, cochainDesc_precomp, cochainDesc_precomp, cochainDesc_precomp]
        exact map_add (s.π.app (op j)).hom x y }

set_option backward.isDefEq.respectTransparency false in
/-- The evaluated native Hom cone is limiting without arbitrary shape limits. -/
def evaluatedColimitConeIsLimit :
    IsLimit ((eval AddCommGrpCat (.up ℤ) n).mapCone (colimitCone F I)) where
  lift := evaluatedColimitConeLift F I n
  fac s j := by
    ext x
    exact cochainDesc_precomp F I n (fun j => s.π.app (op j) x)
      (evaluatedCone_compatible F I n s x) j.unop
  uniq s m hm := by
    ext x
    change (m x : Cochain (colimit F) I n) =
      cochainDesc F I n (fun j => s.π.app (op j) x) (evaluatedCone_compatible F I n s x)
    apply cochain_ext_colimit F I n
    intro j
    rw [cochainDesc_precomp]
    exact congrArg (fun a => a x) (hm (op j))

/-- Existence of these particular evaluated limits retains independent universes. -/
instance hasLimit_evaluatedInverseDiagram :
    HasLimit (inverseDiagram F I ⋙ eval AddCommGrpCat (.up ℤ) n) :=
  ⟨⟨_, evaluatedColimitConeIsLimit F I n⟩⟩

end CochainComplex.HomComplex
