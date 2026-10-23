/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Grassmannian.Flat

/-!
# Smoothness and flatness of the Grassmannian

The instance in `Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies the premise
`Module.Grassmannian.BaseChangeMkQFormula`, so the declarations below state, with no hypothesis,
that the coordinate chart rings are polynomial rings or zero, and that the glued Grassmannian is
smooth and flat over its base. Their axioms are guarded.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.GrassmannianFlat

/-- The chart at an injective coordinate tuple is the polynomial ring in the free coordinates. -/
def chartRingEquivMvPolynomial (R : Type u) [CommRing R] {k n : ℕ} {I : Fin k → Fin n}
    (hI : Function.Injective I) :
    Module.Grassmannian.ChartRing R (Module.Grassmannian.coordinateTuple R I) ≃ₐ[R]
      MvPolynomial {aj : Fin k × Fin n // aj.2 ∉ Set.range I} R :=
  Module.Grassmannian.chartRingEquivMvPolynomial R hI

/-- The chart at a non-injective coordinate tuple is the zero ring. -/
theorem subsingleton_chartRing (R : Type u) [CommRing R] {k n : ℕ} {I : Fin k → Fin n}
    (hI : ¬ Function.Injective I) :
    Subsingleton (Module.Grassmannian.ChartRing R (Module.Grassmannian.coordinateTuple R I)) :=
  Module.Grassmannian.subsingleton_chartRing hI

/-- The Grassmannian is smooth over its base. -/
theorem smooth_toBase (R : CommRingCat.{u}) (k n : ℕ) : Smooth (Grassmannian.toBase R k n) :=
  inferInstance

/-- The Grassmannian is flat over its base. -/
theorem flat_toBase (R : CommRingCat.{u}) (k n : ℕ) : Flat (Grassmannian.toBase R k n) :=
  inferInstance

/-- The same, for the Grassmannian as a scheme over `Spec R`. -/
theorem flat_schemeOver_hom (R : CommRingCat.{u}) (k n : ℕ) :
    Flat (Grassmannian.schemeOver R k n).hom :=
  inferInstance

end AglibTest.GrassmannianFlat

/-- info: 'AglibTest.GrassmannianFlat.chartRingEquivMvPolynomial' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianFlat.chartRingEquivMvPolynomial

/-- info: 'AglibTest.GrassmannianFlat.subsingleton_chartRing' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianFlat.subsingleton_chartRing

/-- info: 'AglibTest.GrassmannianFlat.smooth_toBase' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianFlat.smooth_toBase

/-- info: 'AglibTest.GrassmannianFlat.flat_toBase' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianFlat.flat_toBase

/-- info: 'AglibTest.GrassmannianFlat.flat_schemeOver_hom' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianFlat.flat_schemeOver_hom

/-- info: 'Module.Grassmannian.smooth_chartRing' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.smooth_chartRing
