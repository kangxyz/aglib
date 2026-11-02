/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.RightDerived.Represented
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Unit

/-!
# Intrinsic additive global sections

Global sections are represented by the exact constant-integer sheaf used in
Mathlib's `Sheaf.H`. No terminal site object is selected. With enough injectives,
the original Ext groups compare with the native right-derived represented
functor, preserving coefficient maps and the original degree-zero unit.

For module sheaves, represented additive sections use the existing lifted unit
over the unchanged scalar sheaf. This does not identify a global scalar ring
or construct an additional module action. Terminal evaluation is an optional
comparison in `Terminal.Comparison`.
-/

@[expose] public noncomputable section

universe u v a e r w

open CategoryTheory CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{a}]

/-- Intrinsic additive global sections, represented by Mathlib's original integer sheaf. -/
abbrev globalGamma : Sheaf J AddCommGrpCat.{a} ⥤ AddCommGrpCat.{max u a} :=
  additiveGamma ((constantSheaf J AddCommGrpCat.{a}).obj
    (AddCommGrpCat.of (ULift.{a} ℤ)))

variable {J} [HasExt.{e} (Sheaf J AddCommGrpCat.{a})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{a})]

/-- Original sheaf cohomology computes the actual right-derived intrinsic global sections. -/
abbrev globalGammaHAddEquiv (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ) :
    H.{e} F n ≃+ ((globalGamma J).rightDerived n).obj F :=
  CategoryTheory.Abelian.extRightDerivedRepresentedAddEquiv _ F n

/-- The intrinsic comparison retains Mathlib's original coefficient map on `Sheaf.H`. -/
lemma globalGammaHAddEquiv_naturality {F G : Sheaf J AddCommGrpCat.{a}}
    (f : F ⟶ G) (n : ℕ) (x : H.{e} F n) :
    globalGammaHAddEquiv G n (H.map f n x) =
      ((globalGamma J).rightDerived n).map f (globalGammaHAddEquiv F n x) :=
  CategoryTheory.Abelian.extRightDerivedRepresentedAddEquiv_naturality _ f n x

/-- An original morphism from the integer sheaf gives the original degree-zero unit. -/
lemma globalGammaHAddEquiv_mk₀ {F : Sheaf J AddCommGrpCat.{a}}
    (f : (constantSheaf J AddCommGrpCat.{a}).obj
      (AddCommGrpCat.of (ULift.{a} ℤ)) ⟶ F) :
    globalGammaHAddEquiv F 0 (Ext.mk₀ f) =
      (globalGamma J).toRightDerivedZero.app F f :=
  CategoryTheory.Abelian.extRightDerivedRepresentedAddEquiv_mk₀ f

end CategoryTheory.Sheaf

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r})

/-- Intrinsic additive sections of modules, represented by the actual lifted rank-one sheaf. -/
abbrev representedGamma : SheafOfModules.{max r w} R ⥤ AddCommGrpCat.{max u r w} :=
  CategoryTheory.additiveGamma (liftedUnit.{u, v, w, r} R)

end SheafOfModules
