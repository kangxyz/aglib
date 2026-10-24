/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars

/-!
# Original degree-zero module cohomology and terminal sections

The native additive equivalence `Sheaf.H.equiv₀` is linear for the canonical
coefficient action on the original cohomology. Its target consists of the
original module sections at a terminal object. The coefficient-ring universe
and the original Ext universe remain independent of the site and section
universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf

universe u v r e

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [CommRing R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

attribute [local instance] hasSheafify cohomologyModule

/-- The original degree-zero cohomology is linearly equivalent to the original
module sections at a terminal object, without resizing either carrier. -/
def degreeZeroSectionsLinearEquiv (F : Sheaf J (ModuleCat.{max u v} R))
    {T : C} (hT : IsTerminal T) :
    CategoryTheory.Sheaf.H.{e} ((underlying R J).obj F) 0 ≃ₗ[R]
      F.obj.obj (op T) where
  toAddEquiv := CategoryTheory.Sheaf.H.equiv₀ ((underlying R J).obj F) hT
  map_smul' r x := by
    let E : CategoryTheory.Sheaf.H.{e} ((underlying R J).obj F) 0 ≃+
        F.obj.obj (op T) :=
      CategoryTheory.Sheaf.H.equiv₀ ((underlying R J).obj F) hT
    change E (r • x) = r • E x
    rw [cohomology_smul J R F 0 r x]
    exact (CategoryTheory.Sheaf.H.equiv₀_naturality hT
      ((underlying R J).map (r • 𝟙 F)) x).symm

/-- The forward map is the unchanged native degree-zero evaluation. -/
@[simp]
theorem degreeZeroSectionsLinearEquiv_apply
    (F : Sheaf J (ModuleCat.{max u v} R)) {T : C} (hT : IsTerminal T)
    (x : CategoryTheory.Sheaf.H.{e} ((underlying R J).obj F) 0) :
    degreeZeroSectionsLinearEquiv J R F hT x =
      CategoryTheory.Sheaf.H.equiv₀ ((underlying R J).obj F) hT x := rfl

/-- The inverse map is the unchanged native section-to-cohomology map. -/
@[simp]
theorem degreeZeroSectionsLinearEquiv_symm_apply
    (F : Sheaf J (ModuleCat.{max u v} R)) {T : C} (hT : IsTerminal T)
    (x : F.obj.obj (op T)) :
    (degreeZeroSectionsLinearEquiv J R F hT).symm x =
      (CategoryTheory.Sheaf.H.equiv₀ ((underlying R J).obj F) hT).symm x := rfl

/-- Coefficient naturality uses the original module cohomology and section maps. -/
theorem degreeZeroSectionsLinearEquiv_naturality
    {F G : Sheaf J (ModuleCat.{max u v} R)} (f : F ⟶ G)
    {T : C} (hT : IsTerminal T)
    (x : CategoryTheory.Sheaf.H.{e} ((underlying R J).obj F) 0) :
    degreeZeroSectionsLinearEquiv J R G hT ((cohomology J R 0).map f x) =
      f.hom.app (op T) (degreeZeroSectionsLinearEquiv J R F hT x) :=
  (CategoryTheory.Sheaf.H.equiv₀_naturality hT ((underlying R J).map f) x).symm

end ModuleCat.Sheaf
