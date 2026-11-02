/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
public import Aglib.Algebra.Homology.RightDerived.Postcomp

/-! # Higher direct image through a finite outer morphism

This is the finite-target reduction, not composition with a finite inner map.
It uses the original natural-degree derived functors on their installed
injective resolutions. No additional derived-category or Ext realization is
selected. The exact finite direct image is not assumed to reflect zero.
Global sections are evaluated at the original identity etale objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

variable {Y X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (k : Y ⟶ X) (q : ℕ)

/-- The finite outer direct image commutes with the original higher image.
The first factor derives the actual direct-image composition comparison;
the second is exact postcomposition on the same injective resolution. -/
def higherDirectImageFiniteOuterIso :
    higherDirectImage (k ≫ f) q ≅ higherDirectImage k q ⋙ directImage f :=
  Functor.rightDerivedNatIsoOfAdditive (directImageCompIso f k).symm q ≪≫
    Functor.rightDerivedPostcompIso (directImage k) (directImage f) q

/-- Only the forward zero implication is needed: no zero-reflection property
of finite direct image is imposed or inferred. -/
theorem higherDirectImage_comp_isZero_of_finite_outer
    (M : AbelianSheaf.{u, u + 1} Y)
    (h : IsZero ((higherDirectImage k q).obj M)) :
    IsZero ((higherDirectImage (k ≫ f) q).obj M) :=
  ((directImage f).map_isZero h).of_iso
    ((higherDirectImageFiniteOuterIso f k q).app M)

/-- Global sections on `S` of the original composite higher image are the
actual global sections on `X` of the inner higher image. These are sections
at the identity etale objects, not sections on an unspecified refinement. -/
def finiteOuterHigherGlobalSectionsIso (M : AbelianSheaf.{u, u + 1} Y) :
    (globalSections S).obj ((higherDirectImage (k ≫ f) q).obj M) ≅
      (globalSections X).obj ((higherDirectImage k q).obj M) :=
  (globalSections S).mapIso ((higherDirectImageFiniteOuterIso f k q).app M) ≪≫
    (directImageGlobalSectionsIso f).app ((higherDirectImage k q).obj M)

/-- The comparison uses exactly the two original component maps. -/
theorem finiteOuterHigherGlobalSectionsIso_hom
    (M : AbelianSheaf.{u, u + 1} Y) :
    (finiteOuterHigherGlobalSectionsIso f k q M).hom =
      (globalSections S).map ((higherDirectImageFiniteOuterIso f k q).hom.app M) ≫
        (directImageGlobalSectionsIso f).hom.app ((higherDirectImage k q).obj M) := rfl

/-- A fixed original higher-image section is zero exactly when its actual
finite-target section is zero. This does not assert that a ramified finite
map, composed with an etale cover, becomes etale. -/
theorem finiteOuterHigherGlobalSectionsIso_eq_zero_iff
    (M : AbelianSheaf.{u, u + 1} Y)
    (ξ : (globalSections S).obj ((higherDirectImage (k ≫ f) q).obj M)) :
    (finiteOuterHigherGlobalSectionsIso f k q M).hom ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    apply (ConcreteCategory.bijective_of_isIso
      (finiteOuterHigherGlobalSectionsIso f k q M).hom).1
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
