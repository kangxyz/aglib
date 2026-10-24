/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Elements of native limits of complexes of abelian groups

Compatible element families are transported through the native limit universal
property, after evaluation and the forgetful functor. No alternate complex or
limit carrier is introduced.
-/

@[expose] public noncomputable section

universe w w' u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {J : Type w} [Category.{w'} J]
  (F : J ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
  [∀ n : ℤ, HasLimit (F ⋙ eval AddCommGrpCat (.up ℤ) n)] [HasLimit F]

/-- A compatible family gives an element of the actual limit complex. -/
def limitElement (n : ℤ) (x : ∀ j, (F.obj j).X n)
    (hx : ∀ (j k : J) (f : j ⟶ k), (F.map f).f n (x j) = x k) :
    (limit F).X n :=
  (Types.isLimitEquivSections
    (isLimitOfPreserves
      (eval AddCommGrpCat (.up ℤ) n ⋙ forget AddCommGrpCat)
      (limit.isLimit F))).symm ⟨x, fun {j k} f => hx j k f⟩

set_option backward.isDefEq.respectTransparency false in
/-- Projection recovers the original family without changing the limit. -/
lemma limitElement_π (n : ℤ) (x : ∀ j, (F.obj j).X n)
    (hx : ∀ (j k : J) (f : j ⟶ k), (F.map f).f n (x j) = x k) (j : J) :
    (limit.π F j).f n (limitElement F n x hx) = x j :=
  Types.isLimitEquivSections_symm_apply
    (isLimitOfPreserves
      (eval AddCommGrpCat (.up ℤ) n ⋙ forget AddCommGrpCat)
      (limit.isLimit F)) ⟨x, fun {j k} f => hx j k f⟩ j

/-- Elements of the actual limit are determined by all their projections. -/
lemma limitElement_ext (n : ℤ) (x y : (limit F).X n)
    (h : ∀ j, (limit.π F j).f n x = (limit.π F j).f n y) : x = y :=
  Concrete.isLimit_ext _
    (isLimitOfPreserves (eval AddCommGrpCat (.up ℤ) n) (limit.isLimit F)) x y h

end CochainComplex
