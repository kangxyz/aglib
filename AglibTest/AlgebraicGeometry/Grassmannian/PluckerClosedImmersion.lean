/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Grassmannian.PluckerClosedImmersion

/-!
# The Plücker morphism is a closed immersion

The declarations below restate the chart description of the Plücker morphism (a point lies in the
chart at a `k`-subset `S` exactly when its Plücker point lies in the rank-one chart at `p_S`; the
square of charts is a pullback; the chart ring map is surjective), the closed-immersion property,
and the properness and separatedness of the Grassmannian over `Spec R`, and guard their axioms.
The instance in `Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies the premise
`Module.Grassmannian.BaseChangeMkQFormula`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Limits AlgebraicGeometry TensorProduct
open scoped Module.Grassmannian

universe u

namespace AglibTest.GrassmannianPluckerClosedImmersion

/-- A commuting square over `Spec R` with the lifting property on affine points is a pullback. -/
theorem isPullback_of_lift {R : CommRingCat.{u}} {W X Y Z : Over (Spec R)} (i : W ⟶ X)
    (φ : W ⟶ Z) (f : X ⟶ Y) (j : Z ⟶ Y) [Mono i] (w : i ≫ f = φ ≫ j)
    (H : ∀ (A : CommAlgCat.{u} R) (a : (algSpec R).obj (op A) ⟶ X)
      (b : (algSpec R).obj (op A) ⟶ Z), a ≫ f = b ≫ j →
        ∃ c : (algSpec R).obj (op A) ⟶ W, c ≫ i = a ∧ c ≫ φ = b) :
    IsPullback i.left φ.left f.left j.left :=
  AlgSpecPoints.isPullback_of_lift i φ f j w H

/-- A point lies in the chart at `S` exactly when its Plücker point lies in the rank-one chart at
`p_S`. -/
theorem mem_chart_iff_pluckerFin_mem_chart (R : CommRingCat.{u}) {k n : ℕ} {A : Type u}
    [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] (Fin n → R); A))
    (S : Set.powersetCard (Fin n) k) :
    N ∈ Module.Grassmannian.chart A (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (Grassmannian.pluckerChartIndex S))) ↔
      Grassmannian.pluckerFinPoint N ∈ Module.Grassmannian.chart A
        (Module.Grassmannian.baseChangeTuple A
          (Module.Grassmannian.coordinateTuple R (Grassmannian.pluckerTargetIndex k S))) :=
  ⟨Grassmannian.pluckerFin_mem_chart_of_mem_chart S,
    Grassmannian.mem_chart_of_pluckerFin_mem_chart N S⟩

/-- The chart at `S` is the preimage of the rank-one chart at `p_S`. -/
theorem isPullback_pluckerChart (R : CommRingCat.{u}) {k n : ℕ}
    (S : Set.powersetCard (Fin n) k) :
    IsPullback (Grassmannian.chartι (Grassmannian.pluckerChart k n S)).left
      (Grassmannian.pluckerChartHom (R := R) S).left (Grassmannian.plucker R k n).left
      (Grassmannian.chartι (Grassmannian.pluckerTargetChart k n S)).left :=
  Grassmannian.isPullback_pluckerChart R S

/-- On charts, the Plücker morphism is surjective on coordinate rings. -/
theorem pluckerChartAlgHom_surjective (R : CommRingCat.{u}) {k n : ℕ}
    (S : Set.powersetCard (Fin n) k) :
    Function.Surjective (Grassmannian.pluckerChartAlgHom (R := R) S).hom :=
  Grassmannian.pluckerChartAlgHom_surjective S

/-- The Plücker morphism is a closed immersion. -/
theorem isClosedImmersion_plucker (R : CommRingCat.{u}) (k n : ℕ) :
    IsClosedImmersion (Grassmannian.plucker R k n).left :=
  inferInstance

/-- The Plücker morphism into `P(⋀^k R^n)` is a closed immersion. -/
theorem isClosedImmersion_pluckerProjective (R : CommRingCat.{u}) (k n : ℕ) :
    IsClosedImmersion (Grassmannian.pluckerProjective R k n).left :=
  inferInstance

/-- The Grassmannian is proper over `Spec R`. -/
theorem isProper_toBase (R : CommRingCat.{u}) (k n : ℕ) :
    IsProper (Grassmannian.toBase R k n) :=
  inferInstance

/-- The Grassmannian is separated over `Spec R`. -/
theorem isSeparated_schemeOver_hom (R : CommRingCat.{u}) (k n : ℕ) :
    IsSeparated (Grassmannian.schemeOver R k n).hom :=
  inferInstance

end AglibTest.GrassmannianPluckerClosedImmersion

/-- info: 'AglibTest.GrassmannianPluckerClosedImmersion.isPullback_of_lift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPluckerClosedImmersion.isPullback_of_lift

/-- info: 'AglibTest.GrassmannianPluckerClosedImmersion.mem_chart_iff_pluckerFin_mem_chart'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPluckerClosedImmersion.mem_chart_iff_pluckerFin_mem_chart

/-- info: 'AglibTest.GrassmannianPluckerClosedImmersion.isPullback_pluckerChart' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPluckerClosedImmersion.isPullback_pluckerChart

/-- info: 'AglibTest.GrassmannianPluckerClosedImmersion.pluckerChartAlgHom_surjective' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPluckerClosedImmersion.pluckerChartAlgHom_surjective

/-- info: 'AglibTest.GrassmannianPluckerClosedImmersion.isClosedImmersion_plucker' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPluckerClosedImmersion.isClosedImmersion_plucker

/-- info: 'AglibTest.GrassmannianPluckerClosedImmersion.isClosedImmersion_pluckerProjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPluckerClosedImmersion.isClosedImmersion_pluckerProjective

/-- info: 'AglibTest.GrassmannianPluckerClosedImmersion.isProper_toBase' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPluckerClosedImmersion.isProper_toBase

/-- info: 'AglibTest.GrassmannianPluckerClosedImmersion.isSeparated_schemeOver_hom' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianPluckerClosedImmersion.isSeparated_schemeOver_hom

/-- info: 'exteriorPower.mapOfIsScalarTower' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exteriorPower.mapOfIsScalarTower
