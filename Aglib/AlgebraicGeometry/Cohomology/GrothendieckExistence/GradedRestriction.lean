/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedHomogeneousAction
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineSections

/-! # Original restrictions of formal graded sections -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite DirectSum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The actual graded piece sections with their original structural base action. -/
abbrev formalGradedSectionsA (n : ℕ) (U : X.Opens) :=
  (moduleSectionsPresheaf X (idealThickeningBaseScalar f) (F.gradedPiece n)).obj (op U)

/-- The section model inherits the original coordinate-ring action on each open. -/
local instance (n : ℕ) (U : X.Opens) :
    Module Γ(X, U) (formalGradedSectionsA f I F n U) :=
  inferInstanceAs (Module Γ(X, U) Γ(F.gradedPiece n, U))

/-- The original degreewise section restriction, over the specified base ring. -/
abbrev formalGradedComponentRestriction (n : ℕ) {U V : X.Opens} (h : U ≤ V) :
    formalGradedSectionsA f I F n V →ₗ[A] formalGradedSectionsA f I F n U :=
  ((moduleSectionsPresheaf X (idealThickeningBaseScalar f) (F.gradedPiece n)).map
    (homOfLE h).op).hom

/-- Restriction of the full graded module is the native direct sum of actual restrictions. -/
def formalGradedSectionsRestriction {U V : X.Opens} (h : U ≤ V) :
    (⨁ n, formalGradedSectionsA f I F n V) →ₗ[A]
      (⨁ n, formalGradedSectionsA f I F n U) :=
  DirectSum.lmap (fun n => formalGradedComponentRestriction f I F n h)

@[simp]
theorem formalGradedSectionsRestriction_of {U V : X.Opens} (h : U ≤ V)
    (n : ℕ) (x : formalGradedSectionsA f I F n V) :
    formalGradedSectionsRestriction f I F h (DirectSum.of _ n x) =
      DirectSum.of _ n (formalGradedComponentRestriction f I F n h x) := by
  exact DirectSum.lmap_of (fun k => formalGradedComponentRestriction f I F k h) n x

/-- All homogeneous scalars commute with the original restriction maps. -/
theorem formalGradedHomogeneousAction_restriction {U V : X.Opens} (h : U ≤ V)
    (r n : ℕ) (a : I.associatedGradedGrading r)
    (x : formalGradedSectionsA f I F n V) :
    formalGradedComponentRestriction f I F (r + n) h
        ((formalGradedHomogeneousAction f I F r n a).app V x) =
      (formalGradedHomogeneousAction f I F r n a).app U
        (formalGradedComponentRestriction f I F n h x) :=
  (PresheafOfModules.naturality_apply (formalGradedHomogeneousAction f I F r n a).val
    (homOfLE h).op x).symm

/-- Original graded restrictions are semilinear over the actual coordinate restriction. -/
theorem formalGradedSectionsRestriction_coordinate_smul {U V : X.Opens} (h : U ≤ V)
    (b : Γ(X, V)) (x : ⨁ n, formalGradedSectionsA f I F n V) :
    formalGradedSectionsRestriction f I F h (b • x) =
      X.presheaf.map (homOfLE h).op b • formalGradedSectionsRestriction f I F h x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x =>
    simp only [← DirectSum.of_smul, formalGradedSectionsRestriction_of]
    congr 1
    exact (F.gradedPiece n).val.map_smul (homOfLE h).op b x
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

end AlgebraicGeometry.Scheme.Cohomology
