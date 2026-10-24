/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.ShortComplexColimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Acyclicity of actual exact colimits of complexes

The imported `ShortComplex.exact_obj_colimit` is a generic exact-colimit
comparison with arbitrary categorical hypotheses. Its current source is in the
continuity family. This temporary ownership debt retains that accepted producer
unchanged and avoids a duplicate implementation; a later coordinated relocation
can lower the import without altering these declarations.
-/

@[expose] public noncomputable section

universe w w' t v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]
  [HasExactColimitsOfShape J C] {ι : Type t} {c : ComplexShape ι}

/-- Exact colimits of acyclic native complexes are acyclic, degree by degree. -/
lemma acyclic_colimit (F : J ⥤ HomologicalComplex C c)
    (hF : ∀ j, (F.obj j).Acyclic) : (colimit F).Acyclic := by
  intro n
  have : PreservesColimit F (shortComplexFunctor C c n ⋙ ShortComplex.π₁) :=
    inferInstanceAs (PreservesColimit F (eval C c (c.prev n)))
  have : PreservesColimit F (shortComplexFunctor C c n ⋙ ShortComplex.π₂) :=
    inferInstanceAs (PreservesColimit F (eval C c n))
  have : PreservesColimit F (shortComplexFunctor C c n ⋙ ShortComplex.π₃) :=
    inferInstanceAs (PreservesColimit F (eval C c (c.next n)))
  exact ShortComplex.exact_obj_colimit (shortComplexFunctor C c n) F (fun j => hF j n)

end HomologicalComplex
