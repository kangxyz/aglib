/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Positive shifted Hom from a projective single

The native same-degree single of a projective object has no maps to positive shifts
of any coefficient single. The proof uses the original single-functor shift and
localization comparisons and the existing single-object projectivity vanishing.
No Ext-size, enough-projectives, enough-injectives or coefficient-projectivity
hypothesis is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A projective single has no original morphism to a positive shift in the same degree. -/
theorem from_singleFunctor_shift_eq_zero_of_projective (P V : C) [Projective P]
    (n i : ℤ) (hi : 0 < i)
    (f : (singleFunctor C n).obj P ⟶ ((singleFunctor C n).obj V)⟦i⟧) : f = 0 := by
  let eP := (singleFunctorIsoCompQ C n).app P
  let eV := ((singleFunctors C).shiftIso i (n - i) n (by omega)).app V ≪≫
    (singleFunctorIsoCompQ C (n - i)).app V
  have h := from_singleFunctor_obj_eq_zero_of_projective
    (eP.inv ≫ f ≫ eV.hom) (n - i) (by omega)
  apply (cancel_epi eP.inv).mp
  apply (cancel_mono eV.hom).mp
  simpa only [Category.assoc, zero_comp, comp_zero] using h

/-- The same original positive shifted-Hom group is zero, without a global resolution input. -/
theorem subsingleton_shiftedHom_singleFunctor_of_projective (P V : C) [Projective P]
    (n i : ℤ) (hi : 0 < i) :
    Subsingleton ((singleFunctor C n).obj P ⟶ ((singleFunctor C n).obj V)⟦i⟧) :=
  subsingleton_of_forall_eq 0
    (from_singleFunctor_shift_eq_zero_of_projective P V n i hi)

end DerivedCategory
