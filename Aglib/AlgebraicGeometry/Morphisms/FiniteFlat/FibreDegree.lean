/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.FunctionField
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankOne
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree

/-!
# Fibre degree of a finite flat morphism

For a finite flat locally finitely presented dominant morphism between integral
schemes, every field-valued fibre has degree equal to the actual function-field
degree. The proof uses the native locally constant rank and the original
generic-fibre coordinate equivalence. Flatness is essential: normality of the
target alone does not bound special fibre length by the generic degree.

The theta incidence argument uses this on a nonempty flat open. No assertion
about the fibres outside that open follows from the theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteFlat

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]

/-- The degree of the actual field-valued fibre is the native finite-flat rank.
The field need not be algebraically closed, and nilpotent lengths are retained. -/
theorem finiteSchemeDegree_fibre_eq_finrank (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Y) :
    finiteSchemeDegree K (pullback.snd f p) = f.finrank (p default) :=
  (nativeRank_geometricFibre f K p).symm

variable [IsIntegral X] [IsIntegral Y] [IsDominant f]

/-- Native finite-flat rank at the generic point is the degree of the original
function-field embedding. No separately supplied base-change theorem is needed. -/
theorem finrank_genericPoint_eq_functionFieldDegree :
    f.finrank (genericPoint Y) = functionFieldDegree f := by
  let p := Y.fromSpecStalk (genericPoint Y)
  have hp : p (default : Spec (.of Y.functionField)) = genericPoint Y := by
    exact (congrArg p (Subsingleton.elim (default : Spec (.of Y.functionField))
      (IsLocalRing.closedPoint Y.functionField))).trans Y.fromSpecStalk_closedPoint
  have hr := nativeRank_geometricFibre f Y.functionField p
  rw [hp] at hr
  let := Scheme.functionFieldMapAlgebra f
  let : Algebra Y.functionField Γ((genericFibreScheme f).left, ⊤) :=
    coordinateAlgebra Y.functionField (genericFibreScheme f)
  exact hr.trans
    (genericFibreCoordinatesEquiv f finiteDominantGenericFibre).toLinearEquiv.finrank_eq

variable [LocallyOfFinitePresentation f]

/-- Every native rank equals the function-field degree on the integral target.
This is the valid constant-length statement for a finite flat family. -/
theorem finrank_eq_functionFieldDegree (y : Y) :
    f.finrank y = functionFieldDegree f :=
  ((f.isLocallyConstant_finrank).apply_eq_of_preconnectedSpace y (genericPoint Y)).trans
    (finrank_genericPoint_eq_functionFieldDegree f)

/-- Every actual field-valued fibre of a finite flat locally finitely presented
dominant morphism of integral schemes has the same degree as its function-field
extension. In particular, this counts scheme length, not merely geometric points. -/
theorem finiteSchemeDegree_fibre_eq_functionFieldDegree (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ Y) :
    finiteSchemeDegree K (pullback.snd f p) = functionFieldDegree f :=
  (finiteSchemeDegree_fibre_eq_finrank f K p).trans
    (finrank_eq_functionFieldDegree f (p default))

/-- A finite flat locally finitely presented dominant map of integral schemes
with function-field degree one is an isomorphism of the original schemes. -/
theorem isIso_of_functionFieldDegree_eq_one (h : functionFieldDegree f = 1) : IsIso f := by
  apply (Scheme.Hom.isIso_iff_finrank_eq f).mpr
  ext y
  exact (finrank_eq_functionFieldDegree f y).trans h

end AlgebraicGeometry.Scheme.Hom.FiniteFlat
