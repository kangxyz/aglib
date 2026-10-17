/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Grassmannian.Chart
public import Aglib.RingTheory.Grassmannian.Overlap
public import Aglib.RingTheory.Grassmannian.Covering
public import Aglib.RingTheory.Grassmannian.Gluing
public import Aglib.RingTheory.Grassmannian.ChartLocus
public import Aglib.AlgebraicGeometry.Grassmannian.Overlap
public import Aglib.AlgebraicGeometry.Grassmannian.Gluing

/-! Focused checks for the Grassmannian charts. Statements about Mathlib's `map` assume the named
premise `Module.Grassmannian.BaseChangeMkQFormula` (the component formula of Mathlib's unexposed
`baseChangeMkQ`); this file does not use the instance in `BaseChangeFormula`. Checked: the
chart is a subfunctor of Mathlib's actual `Module.Grassmannian.functor`, it is corepresented by
the chart ring, base change of a point cut
out by a linear section is computed by composition, the overlap criterion is a unit
determinant, the coordinate charts cover locally, Mathlib's functor is separated and glues for
finite standard covers, and the chart scheme represents the chart functor on all of
`Over (Spec R)`. -/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct AlgebraicGeometry
open scoped Module.Grassmannian

universe u v w

section General

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, v, w} R M]

/-- The chart functor is a subfunctor of Mathlib's Grassmannian functor itself. -/
example (x : Fin k → M) :
    Subfunctor (Module.Grassmannian.functor.{u, v, w} (R := R) (M := M) k) :=
  Module.Grassmannian.chartFunctor R x

example (x : Fin k → M) (A : CommAlgCat.{w} R) (N : G(k, A ⊗[R] M; A)) :
    N ∈ (Module.Grassmannian.chartFunctor.{u, v, w} R x).obj A ↔
      Function.Bijective
        (Module.Grassmannian.chartMap (fun b ↦ (1 : A) ⊗ₜ[R] x b) N.toSubmodule) :=
  Iff.rfl

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Mathlib's base change `Module.Grassmannian.map` of the point cut out by `φ`. -/
example (f : A →ₐ[R] B) (x : Fin k → M) (φ : M →ₗ[R] (Fin k → A))
    (hφ : ∀ b, φ (x b) = Pi.single b 1) :
    Module.Grassmannian.map f (Module.Grassmannian.ofChartSection φ hφ) =
      Module.Grassmannian.ofChartSection (f.toLinearMap.compLeft (Fin k) ∘ₗ φ)
        (Module.Grassmannian.compLeft_mem_chartSections f hφ) :=
  Module.Grassmannian.map_ofChartSection f φ hφ

example (x : Fin k → M) :
    Module.Grassmannian.chart A (fun b ↦ (1 : A) ⊗ₜ[R] x b) ≃
      {φ : M →ₗ[R] (Fin k → A) // ∀ b, φ (x b) = Pi.single b 1} :=
  Module.Grassmannian.chartEquiv A x

example (x y : Fin k → M) {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ Module.Grassmannian.chart A (fun b ↦ (1 : A) ⊗ₜ[R] x b)) :
    N ∈ Module.Grassmannian.chart A (fun b ↦ (1 : A) ⊗ₜ[R] y b) ↔
      IsUnit (Matrix.of fun a b ↦ Module.Grassmannian.toChartSection hN (y b) a).det :=
  Module.Grassmannian.mem_chart_iff_isUnit_det hN y

end General

section Free

variable {R : Type u} [CommRing R] {k n : ℕ}
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- The chart of the Grassmannian of `Fin n → R` is corepresented by the chart ring. -/
example (x : Fin k → Fin n → R) :
    (Module.Grassmannian.chartFunctor.{u, u, u} R x).toFunctor.CorepresentableBy
      (CommAlgCat.of R (Module.Grassmannian.ChartRing R x)) :=
  Module.Grassmannian.chartFunctorCorepresentableBy R x

/-- The chart relations are the entries of `Φ X - 1`. -/
example (x : Fin k → Fin n → R) (a b : Fin k) :
    Module.Grassmannian.chartRelation R x a b =
      ∑ j, x b j • (MvPolynomial.X (a, j) : MvPolynomial (Fin k × Fin n) R) -
        if a = b then 1 else 0 :=
  rfl

/-- The coordinate charts cover: every point is, near every prime, in a coordinate chart. -/
example {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] (Fin n → R); A))
    (p : PrimeSpectrum A) :
    ∃ (I : Fin k → Fin n) (r : A), r ∉ p.asIdeal ∧
      ∀ {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B), IsUnit (f r) →
        Module.Grassmannian.map f N ∈ Module.Grassmannian.chart B
          (fun b ↦ (1 : B) ⊗ₜ[R] (Pi.single (I b) 1 : Fin n → R)) :=
  Module.Grassmannian.exists_mem_chart_map N p

/-- The intersection of two charts is corepresented by a localization of the first chart ring. -/
example (x y : Fin k → Fin n → R) :
    (Module.Grassmannian.chartFunctor.{u, u, u} R x ⊓
        Module.Grassmannian.chartFunctor R y).toFunctor.CorepresentableBy
      (CommAlgCat.of R (Localization.Away (Module.Grassmannian.chartTransitionDet x y))) :=
  Module.Grassmannian.chartInterCorepresentableBy R x y

/-- The transition isomorphism between the two coordinate rings of a chart intersection does not
change the underlying point of Mathlib's Grassmannian. -/
example (x y : Fin k → Fin n → R) {A : CommAlgCat.{u} R}
    (Φ : CommAlgCat.of R (Localization.Away (Module.Grassmannian.chartTransitionDet y x)) ⟶ A) :
    ((Module.Grassmannian.chartInterCorepresentableBy R x y).homEquiv
        ((Module.Grassmannian.chartTransitionIso R x y).hom ≫ Φ)).1 =
      ((Module.Grassmannian.chartInterCorepresentableBy R y x).homEquiv Φ).1 :=
  Module.Grassmannian.chartInterCorepresentableBy_homEquiv_transitionIso_hom x y Φ

/-- Finite intersections of charts, for instance triple overlaps, are corepresented by
localizations of one chart ring. -/
example {ι : Type*} [Fintype ι] (x : Fin k → Fin n → R) (y : ι → Fin k → Fin n → R) :
    (Module.Grassmannian.chartFunctor.{u, u, u} R x ⊓
        ⨅ i, Module.Grassmannian.chartFunctor R (y i)).toFunctor.CorepresentableBy
      (CommAlgCat.of R (Localization.Away (∏ i, Module.Grassmannian.chartTransitionDet x (y i)))) :=
  Module.Grassmannian.chartFamilyInterCorepresentableBy R x y

/-- The gluing identities at a single chart: the self-overlap is everything and the
self-transition is the identity. -/
example (x : Fin k → Fin n → R) :
    IsUnit (Module.Grassmannian.chartTransitionDet x x) ∧
      Module.Grassmannian.chartTransitionIso R x x = Iso.refl _ :=
  ⟨Module.Grassmannian.isUnit_chartTransitionDet_self x,
    Module.Grassmannian.chartTransitionIso_self x⟩

example (x y : Fin k → Fin n → R) :
    Module.Grassmannian.chartTransitionDet x y =
      (Matrix.of fun a b ↦ ∑ j, y b j • Module.Grassmannian.chartCoordinate x a j).det :=
  rfl

end Free

section Locus

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
variable {A : Type w} [CommRing A] [Algebra R A]
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, v, w} R M]

/-- Membership in a chart is Zariski local. -/
example {ι : Type*} (s : ι → A) (hs : Ideal.span (Set.range s) = ⊤) (y : Fin k → M)
    (N : G(k, A ⊗[R] M; A))
    (h : ∀ i, Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N ∈
      Module.Grassmannian.chart (Localization.Away (s i))
        (fun b ↦ (1 : Localization.Away (s i)) ⊗ₜ[R] y b)) :
    N ∈ Module.Grassmannian.chart A (fun b ↦ (1 : A) ⊗ₜ[R] y b) :=
  Module.Grassmannian.mem_chart_of_map_localization s hs y N h

end Locus

section Descent

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
variable {A : Type w} [CommRing A] [Algebra R A]
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, v, w} R M]

/-- Separatedness of Mathlib's Grassmannian functor for standard covers. -/
example {ι : Type*} (s : ι → A) (hs : Ideal.span (Set.range s) = ⊤)
    {N N' : G(k, A ⊗[R] M; A)}
    (h : ∀ i, Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N =
      Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N') :
    N = N' :=
  Module.Grassmannian.eq_of_map_localization_eq s hs h

/-- Gluing for Mathlib's Grassmannian functor along a finite standard cover, with the overlaps
`Localization.Away (s i * s j)`-style rings given as localizations of `A_{s j}` away from
`s i`. -/
example {ι : Type*} [Finite ι] (s : ι → A) (hs : Ideal.span (Set.range s) = ⊤)
    (N : ∀ i, G(k, Localization.Away (s i) ⊗[R] M; Localization.Away (s i)))
    (C : ι → ι → Type w) [∀ i j, CommRing (C i j)] [∀ i j, Algebra R (C i j)]
    [∀ i j, Algebra (Localization.Away (s j)) (C i j)]
    [∀ i j, IsScalarTower R (Localization.Away (s j)) (C i j)]
    [∀ i j, IsLocalization.Away (algebraMap A (Localization.Away (s j)) (s i)) (C i j)]
    (e : ∀ i j, Localization.Away (s i) →ₐ[R] C i j)
    (he : ∀ i j, (e i j).comp (IsScalarTower.toAlgHom R A (Localization.Away (s i))) =
      (IsScalarTower.toAlgHom R (Localization.Away (s j)) (C i j)).comp
        (IsScalarTower.toAlgHom R A (Localization.Away (s j))))
    (hN : ∀ i j, Module.Grassmannian.map (e i j) (N i) =
      Module.Grassmannian.map (IsScalarTower.toAlgHom R (Localization.Away (s j)) (C i j)) (N j)) :
    ∃ N₀ : G(k, A ⊗[R] M; A), ∀ i,
      Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away (s i))) N₀ = N i :=
  Module.Grassmannian.exists_map_localization_eq s hs N C e he hN

end Descent

section Scheme

variable (R : CommRingCat.{u}) {k n : ℕ}
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- The chart scheme represents the chart functor on all schemes over `Spec R`. -/
example (x : Fin k → Fin n → R) :
    ((algΓ R).leftOp ⋙ (Module.Grassmannian.chartFunctor.{u, u, u} R x).toFunctor).RepresentableBy
      ((algSpec R).obj (Opposite.op (CommAlgCat.of R (Module.Grassmannian.ChartRing R x)))) :=
  Grassmannian.chartRepresentableBy R x

/-- The overlap of two charts is an open subscheme of the first chart and represents the
intersection of the chart functors on all schemes over `Spec R`. -/
example (x y : Fin k → Fin n → R) :
    IsOpenImmersion (Grassmannian.chartOverlapToChart R x y).left :=
  Grassmannian.isOpenImmersion_chartOverlapToChart_left R x y

example (x : Fin k → Fin n → R) : IsIso (Grassmannian.chartOverlapToChart R x x).left :=
  Grassmannian.isIso_chartOverlapToChart_self_left R x

example (x y : Fin k → Fin n → R) :
    ((algΓ R).leftOp ⋙ (Module.Grassmannian.chartFunctor.{u, u, u} R x ⊓
      Module.Grassmannian.chartFunctor R y).toFunctor).RepresentableBy
      (Grassmannian.chartOverlapScheme R x y) :=
  Grassmannian.chartOverlapRepresentableBy R x y

/-- The glued Grassmannian: Mathlib's `Scheme.GlueData`, its glued scheme over `Spec R`, the
open charts, and the characterization of maps through charts by their points. -/
example : Scheme.GlueData.{u} := Grassmannian.glueData R k n

example (I : ULift.{u} (Fin k → Fin n)) :
    (Grassmannian.glueData R k n).ι I ≫ Grassmannian.toBase R k n =
      (Grassmannian.chartScheme R (Module.Grassmannian.coordinateTuple R I.down)).hom :=
  Grassmannian.ι_toBase I

example {T : Over (Spec R)} (I J : ULift.{u} (Fin k → Fin n))
    (a : T ⟶ Grassmannian.chartScheme R (Module.Grassmannian.coordinateTuple R I.down))
    (b : T ⟶ Grassmannian.chartScheme R (Module.Grassmannian.coordinateTuple R J.down)) :
    a ≫ Grassmannian.chartι I = b ≫ Grassmannian.chartι J ↔
      ((Grassmannian.chartRepresentableBy R _).homEquiv a).1 =
        ((Grassmannian.chartRepresentableBy R _).homEquiv b).1 :=
  ⟨Grassmannian.point_eq_of_comp_chartι_eq I J a b,
    Grassmannian.comp_chartι_eq_of_point_eq I J a b⟩

/-- On every scheme over `Spec R`, maps into the glued scheme that factor through a coordinate
chart correspond to points of Mathlib's Grassmannian over the global sections that lie in a
coordinate chart. -/
example (T : Over (Spec R)) :
    {g : T ⟶ Grassmannian.schemeOver R k n // ∃ (I : ULift.{u} (Fin k → Fin n))
      (a : T ⟶ Grassmannian.chartScheme R (Module.Grassmannian.coordinateTuple R I.down)),
        g = a ≫ Grassmannian.chartι I} ≃
    {N : (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).obj
        (Opposite.unop ((algΓ R).obj T)) //
      ∃ I : ULift.{u} (Fin k → Fin n), N ∈ (Module.Grassmannian.chartFunctor.{u, u, u} R
        (Module.Grassmannian.coordinateTuple R I.down)).obj (Opposite.unop ((algΓ R).obj T))} :=
  Grassmannian.chartLocalEquiv T

end Scheme

end

/-- info: 'Module.Grassmannian.map_mem_chart' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.map_mem_chart

/-- info: 'Module.Grassmannian.map_ofChartSection' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.map_ofChartSection

/-- info: 'Module.Grassmannian.chartFunctorCorepresentableBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.chartFunctorCorepresentableBy

/-- info: 'Module.Grassmannian.mem_chart_iff_isUnit_det' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.mem_chart_iff_isUnit_det

/-- info: 'AlgebraicGeometry.Grassmannian.chartRepresentableBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.Grassmannian.chartRepresentableBy

/-- info: 'Module.Grassmannian.exists_mem_chart_map' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.exists_mem_chart_map

/-- info: 'Module.Grassmannian.eq_of_map_localization_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.eq_of_map_localization_eq

/-- info: 'Module.Grassmannian.exists_map_localization_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.exists_map_localization_eq

/-- info: 'Module.Grassmannian.chartInterCorepresentableBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.chartInterCorepresentableBy

/-- info: 'Module.Grassmannian.exists_mem_chart_map_of_bijective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.exists_mem_chart_map_of_bijective

/-- info: 'Module.Grassmannian.mem_chart_of_map_localization' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.mem_chart_of_map_localization

/-- info: 'AlgebraicGeometry.Grassmannian.chartOverlapRepresentableBy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.Grassmannian.chartOverlapRepresentableBy

/-- info: 'Module.Grassmannian.chartInterCorepresentableBy_homEquiv_transitionIso_hom' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.chartInterCorepresentableBy_homEquiv_transitionIso_hom

/-- info: 'Module.Grassmannian.chartFamilyInterCorepresentableBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.Grassmannian.chartFamilyInterCorepresentableBy

/-- info: 'AlgebraicGeometry.Grassmannian.glueData' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.glueData

/-- info: 'AlgebraicGeometry.Grassmannian.toBase' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.toBase

/-- info: 'AlgebraicGeometry.Grassmannian.comp_chartι_eq_of_point_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.comp_chartι_eq_of_point_eq

/-- info: 'AlgebraicGeometry.Grassmannian.point_eq_of_comp_chartι_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.point_eq_of_comp_chartι_eq

/-- info: 'AlgebraicGeometry.Grassmannian.chartLocalEquiv' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.chartLocalEquiv

/-- info: 'AlgebraicGeometry.Grassmannian.chartOverlapIso' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.Grassmannian.chartOverlapIso
