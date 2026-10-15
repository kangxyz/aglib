/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.Algebra.Homology.CochainComplexPlus.Single
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Actual injective resolutions and the installed bounded-below derived unit

The supplied native injective resolution, extended by zero, is a bounded-below
complex of injective objects. Its termwise image therefore models the installed
right-derived functor at the original degree-zero single. The comparison uses
the original derived unit and the inverse image of the original resolution
inclusion. Both equations and naturality retain these actual arrows.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory.InjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A] {M N : A}

/-- The actual integer extension of a supplied injective resolution, retaining its bound. -/
def cochainComplexPlus (I : InjectiveResolution M) : CochainComplex.Plus A :=
  ⟨I.cochainComplex, 0, inferInstance⟩

/-- The original resolution inclusion, viewed in bounded-below complexes. -/
def ιPlus (I : InjectiveResolution M) :
    (CochainComplex.singleFunctorPlus A 0).obj M ⟶ I.cochainComplexPlus :=
  ⟨I.ι'⟩

/-- The actual extended chain map associated to a supplied native resolution lift. -/
def Hom.mapPlus {I : InjectiveResolution M} {J : InjectiveResolution N} {f : M ⟶ N}
    (φ : Hom I J f) : I.cochainComplexPlus ⟶ J.cochainComplexPlus :=
  ⟨φ.hom'⟩

theorem ιPlus_naturality {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : Hom I J f) :
    I.ιPlus ≫ φ.mapPlus = (CochainComplex.singleFunctorPlus A 0).map f ≫ J.ιPlus := by
  apply ObjectProperty.hom_ext
  exact φ.ι'_comp_hom'

variable [HasDerivedCategory A]

instance (I : InjectiveResolution M) : IsIso (DerivedCategory.Plus.Q.map I.ιPlus) :=
  Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A) I.ιPlus
    (show QuasiIso I.ι' from inferInstance)

variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]

/-- Termwise application to the actual injective resolution models the installed derived
functor at the original single object. -/
def rightDerivedFunctorPlusIso (I : InjectiveResolution M) :
    DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I.cochainComplexPlus) ≅
      F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) := by
  let := F.isIso_rightDerivedFunctorPlusUnit_of_injective I.cochainComplexPlus
    (fun n ↦ inferInstanceAs (Injective (I.cochainComplex.X n)))
  exact asIso (F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus) ≪≫
    (F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map I.ιPlus))).symm

/-- The model comparison is the original derived unit followed by the inverse image of the
original resolution inclusion. -/
theorem rightDerivedFunctorPlusIso_hom (I : InjectiveResolution M) :
    (rightDerivedFunctorPlusIso F I).hom =
      F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus ≫
        inv (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus)) := by
  simp [rightDerivedFunctorPlusIso]

/-- Composing with the actual derived resolution inclusion recovers the original unit. -/
@[reassoc (attr := simp)]
theorem rightDerivedFunctorPlusIso_hom_comp (I : InjectiveResolution M) :
    (rightDerivedFunctorPlusIso F I).hom ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus) =
      F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus := by
  rw [rightDerivedFunctorPlusIso_hom]
  simp

/-- The comparison preserves the original derived unit on the coefficient single. -/
@[reassoc]
theorem rightDerivedFunctorPlusIso_unit (I : InjectiveResolution M) :
    DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map I.ιPlus) ≫
        (rightDerivedFunctorPlusIso F I).hom =
      F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus A 0).obj M) := by
  apply (cancel_mono
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus))).mp
  rw [Category.assoc, rightDerivedFunctorPlusIso_hom_comp]
  exact F.rightDerivedFunctorPlusUnit.naturality I.ιPlus

/-- Every actual coefficient-resolution lift gives the original derived coefficient map. -/
@[reassoc]
theorem rightDerivedFunctorPlusIso_naturality
    {I : InjectiveResolution M} {J : InjectiveResolution N} {f : M ⟶ N} (φ : Hom I J f) :
    DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ.mapPlus) ≫
        (rightDerivedFunctorPlusIso F J).hom =
      (rightDerivedFunctorPlusIso F I).hom ≫
        F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f) := by
  apply (cancel_mono
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map J.ιPlus))).mp
  rw [Category.assoc, rightDerivedFunctorPlusIso_hom_comp]
  have he := congrArg (fun g ↦ F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g))
    (ιPlus_naturality φ)
  simp only [Functor.map_comp] at he
  change _ = ((rightDerivedFunctorPlusIso F I).hom ≫
    F.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus A 0).map f))) ≫ _
  rw [Category.assoc, ← he, ← Category.assoc, rightDerivedFunctorPlusIso_hom_comp]
  exact F.rightDerivedFunctorPlusUnit.naturality φ.mapPlus

end CategoryTheory.InjectiveResolution
