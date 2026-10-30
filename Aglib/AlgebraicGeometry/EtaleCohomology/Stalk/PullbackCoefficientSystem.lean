/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem
public import Aglib.CategoryTheory.Filtered.SystemConstructions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitCoefficients

/-! # A fixed sheaf pulled back to an inverse scheme diagram

A cone in the opposite category specifies the structural morphisms to a fixed
base scheme. Its fixed coefficient sheaf gives an actual compatible system,
with transitions obtained from the original inverse-image triangle isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u uI vI
attribute [local instance] hasSheafifyLarge

open Continuity

variable {I : Type uI} [Category.{vI} I] (Y : I ⥤ Scheme.{u}ᵒᵖ)
    (b : Cone Y) (F : AbelianSheaf.{u, u + 1} b.pt.unop)

/-- The original inverse-image transition for the fixed coefficient sheaf. -/
def pullbackCoefficientTransition {i j : I} (a : i ⟶ j) :
    (inverseImage (Y.map a).unop).obj ((inverseImage (b.π.app i).unop).obj F) ⟶
      (inverseImage (b.π.app j).unop).obj F :=
  (pullbackTriangleIso (b.π.app j).unop (b.π.app i).unop (Y.map a).unop
    (congrArg Quiver.Hom.unop (b.w a))).inv.app F

/-- The transition remains the same original whole inverse triangle. -/
theorem pullbackCoefficientTransition_eq_generic {i j : I} (a : i ⟶ j) :
    pullbackCoefficientTransition Y b F a =
      InjectiveSystem.System.fixedSourceTransition schemeAdjunctionData Y b F a := by
  exact (congrArg (fun e => e.inv.app F)
    (schemeTriangleIso_eq_pullbackTriangleIso (b.π.app i) (b.π.app j)
      (Y.map a) (b.w a))).symm

/-- Original triangle transitions obey the actual diagram identity comparison. -/
theorem pullbackCoefficientTransition_id (i : I) :
    pullbackCoefficientTransition Y b F (𝟙 i) =
      (diagramInverseImageId Y i).hom.app ((inverseImage (b.π.app i).unop).obj F) := by
  rw [pullbackCoefficientTransition_eq_generic, ← leftIdIso_eq_diagramInverseImageId Y i]
  exact InjectiveSystem.System.fixedSourceTransition_id
    schemeAdjunctionData Y schemeAdjunctionData_coherent b F i

/-- Original triangle transitions obey the actual diagram composition comparison. -/
theorem pullbackCoefficientTransition_comp {i j k : I} (a : i ⟶ j) (d : j ⟶ k) :
    pullbackCoefficientTransition Y b F (a ≫ d) =
      (diagramInverseImageComp Y a d).hom.app ((inverseImage (b.π.app i).unop).obj F) ≫
        (inverseImage (Y.map d).unop).map (pullbackCoefficientTransition Y b F a) ≫
          pullbackCoefficientTransition Y b F d := by
  have h := InjectiveSystem.System.fixedSourceTransition_comp
    schemeAdjunctionData Y schemeAdjunctionData_coherent b F a d
  simp only [← pullbackCoefficientTransition_eq_generic,
    leftCompIso_eq_diagramInverseImageComp, schemeLeft_eq_inverseImage] at h
  exact h

/-- Pulling back one fixed sheaf gives a genuine compatible coefficient system. -/
def pullbackCoefficientSystem : DiagramCoefficientSystem Y :=
  InjectiveSystem.System.fixedSource schemeAdjunctionData Y schemeAdjunctionData_coherent b F

/-- The inverse transition is literally the original triangle identification. -/
@[simp]
theorem diagramInverseTransition_pullbackCoefficientSystem {i j : I} (a : i ⟶ j) :
    diagramInverseTransition Y (pullbackCoefficientSystem Y b F) a =
      pullbackCoefficientTransition Y b F a := by
  exact (InjectiveSystem.System.fixedSource_leftMap
    schemeAdjunctionData Y schemeAdjunctionData_coherent b F a).trans
      (pullbackCoefficientTransition_eq_generic Y b F a).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
