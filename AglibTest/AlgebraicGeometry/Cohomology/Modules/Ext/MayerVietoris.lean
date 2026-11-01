/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.MayerVietoris
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Bifunctor

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

universe u u₁ v₁ u₂ v₂ w₁ w₂

variable (X : Scheme.{u}) (U V : X.Opens)

example : (Scheme.Cohomology.moduleOpenMayerVietorisShortComplex X U V).f =
    biprod.lift
      ((Scheme.Modules.openFreeFunctor X).map (homOfLE inf_le_left))
      (-((Scheme.Modules.openFreeFunctor X).map (homOfLE inf_le_right))) := rfl

example : (Scheme.Cohomology.moduleOpenMayerVietorisShortComplex X U V).g =
    biprod.desc
      ((Scheme.Modules.openFreeFunctor X).map (homOfLE le_sup_left))
      ((Scheme.Modules.openFreeFunctor X).map (homOfLE le_sup_right)) := rfl

example : (Scheme.Cohomology.moduleOpenMayerVietorisShortComplex X U V).ShortExact :=
  Scheme.Cohomology.moduleOpenMayerVietoris_shortExact X U V

example : (Scheme.Cohomology.moduleOpenIntegerMayerVietorisMap X U V).τ₁ =
    Scheme.Cohomology.moduleOpenIntegerMap X (U ⊓ V) := rfl

example : (Scheme.Cohomology.moduleOpenIntegerMayerVietorisMap X U V).τ₃ =
    Scheme.Cohomology.moduleOpenIntegerMap X (U ⊔ V) := rfl

open Scheme.Cohomology in
example (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X (U ⊓ V)) M n) :
    moduleOpenExtCohomologyMap X (U ⊔ V) M (n + 1)
        ((moduleOpenMayerVietoris_shortExact X U V).extClass.comp x (by omega)) =
      (Opens.mayerVietorisSquare U V).δ (moduleAddSheaf X M) n (n + 1) rfl
        (moduleOpenExtCohomologyMap X (U ⊓ V) M n x) :=
  moduleOpenExtCohomologyMap_mayerVietorisDelta X U V M n x

open Scheme.Cohomology in
example (M : X.Modules) (n : ℕ) :
    Ext.contravariantSequence (moduleOpenMayerVietoris_shortExact X U V) M n (n + 1)
        (by omega) ≅
      (Opens.mayerVietorisSquare U V).sequence (moduleAddSheaf X M) n (n + 1) rfl :=
  moduleOpenMayerVietorisSequenceIso X U V M n

section Pairing

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
  {E : Type u₂} [Category.{v₂} E] [Abelian E] [HasExt.{w₂} E]
  (F : C ⥤ X.Modules ⥤ E) [F.Additive] [∀ A, (F.obj A).Additive]
  [∀ A, PreservesFiniteLimits (F.obj A)] [∀ A, PreservesFiniteColimits (F.obj A)]
  [∀ B, PreservesFiniteLimits (F.flip.obj B)]
  [∀ B, PreservesFiniteColimits (F.flip.obj B)]

/-- The sign is the crossing of a degree-p class with this actual source extension. -/
example {A₀ A₁ : C} (M : X.Modules) {p q q' n n' : ℕ}
    (x : Ext.{w₁} A₀ A₁ p) (y : Ext.{u + 1} (Scheme.Modules.openFree X (U ⊓ V)) M q)
    (hq : 1 + q = q') (h : p + q = n) (h' : p + q' = n') :
    F.extBifunctor x
        ((Scheme.Cohomology.moduleOpenMayerVietoris_shortExact X U V).extClass.comp y hq) h' =
      ((-1 : ℤ) ^ p) •
        ((Scheme.Cohomology.moduleOpenMayerVietoris_shortExact X U V).map_of_exact
          (F.obj A₀)).extClass.comp (F.extBifunctor x y h) (by omega) :=
  F.extBifunctor_extClass_comp_right
    (Scheme.Cohomology.moduleOpenMayerVietoris_shortExact X U V) x y hq h h'

end Pairing

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.moduleOpenExtCohomologyMap_mayerVietorisDelta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.moduleOpenExtCohomologyMap_mayerVietorisDelta
