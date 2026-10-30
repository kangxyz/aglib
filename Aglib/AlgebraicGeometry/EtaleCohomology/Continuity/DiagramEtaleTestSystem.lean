/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleTest
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbackSystem

/-! # Actual compatible coefficients on the original stage-test diagram

Restrict the original system to its under-category tail and pull it back along
the native test projections. The inverse-image transitions are the literal
original coefficient-square maps. No coefficient-colimit comparison or
section-continuity premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (i : I)

/-- Restrict the original right-transition system to its actual tail. -/
def diagramCoefficientTail : DiagramCoefficientSystem (diagramSchemeTail X i) :=
  InjectiveSystem.System.restrictAlong schemeAdjunctionData X F (Under.forget i)

/-- The tail's inverse-image transition is still the original transition. -/
theorem diagramInverseTransition_coefficientTail {a b : Under i} (m : a ⟶ b) :
    diagramInverseTransition (diagramSchemeTail X i) (diagramCoefficientTail X F i) m =
      diagramInverseTransition X F m.right := rfl

variable (T : (X.obj i).unop.Etale)

/-- The actual system on the native test schemes, using the original pullback-square maps. -/
def diagramEtaleTestCoefficient : DiagramCoefficientSystem (diagramEtaleTest X i T) :=
  diagramPullbackSystem (diagramSchemeTail X i) (diagramEtaleTest X i T)
    (diagramEtaleTestProjection X i T) (diagramCoefficientTail X F i)

/-- At each stage the coefficient is the original sheaf pulled to the original test chart. -/
theorem diagramEtaleTestCoefficient_obj (a : Under i) :
    (diagramEtaleTestCoefficient X F i T).obj a =
      (inverseImage (diagramEtaleTestChart X i T a).hom).obj (F.obj a.right) := rfl

/-- The test-system transition is exactly the original coefficient-square map. -/
theorem diagramInverseTransition_etaleTest {a b : Under i} (m : a ⟶ b) :
    diagramInverseTransition (diagramEtaleTest X i T) (diagramEtaleTestCoefficient X F i T) m =
      squareCoefficientMap (diagramEtaleTestChart X i T a).hom
        (diagramEtaleTestChart X i T b).hom (X.map m.right).unop
        ((diagramEtaleTest X i T).map m).unop (diagramEtaleTest_map_fst X i T m).symm
        (diagramInverseTransition X F m.right) :=
  diagramInverseTransition_pullbackSystem (diagramSchemeTail X i) (diagramEtaleTest X i T)
    (diagramEtaleTestProjection X i T) (diagramCoefficientTail X F i) m

variable (c : Cocone X)

/-- Restricting the original coefficient diagram is exactly the tail coefficient diagram. -/
def diagramCoefficientTailConeIso :
    coneCoefficientFunctor (diagramSchemeTail X i) (c.whisker (Under.forget i))
        (diagramCoefficientTail X F i) ≅
      Under.forget i ⋙ coneCoefficientFunctor X c F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _m =>
    (Category.comp_id _).trans (Category.id_comp _).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
