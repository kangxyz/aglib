/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.ProjectiveBundle
public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.LocalStructure

/-!
# The Grassmannian of a finite locally free sheaf

The instance in `Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies the premise
`Module.Grassmannian.BaseChangeMkQFormula`. The declarations below restate the functor
`Quot_k(E)` of rank-`k` locally free quotients of a module sheaf `E` on schemes over `S`, its
Zariski sheaf property, its restriction to a trivializing affine chart (F8's `Quot_k(O^n)`,
represented by the Grassmannian), the cover of `S` by such charts when `E` has constant rank `n`,
the representability of `Quot_k(E)` by `Gr(E, k)`, the classification of rank-one quotients by
`P(E) = Gr(E, 1)`, and the local structure of `Gr(E, k)`. Each is guarded for the standard
axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules

universe u

namespace AglibTest.GrassmannianLocallyFree

/-- The functor `Quot_k(E)` on schemes over `S`. -/
def quotBundleFunctor {S : Scheme.{u}} (E : S.Modules) (k : ℕ) : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  Grassmannian.quotBundleFunctor E k

/-- `Quot_k(E)` is a sheaf for the Zariski topology on schemes over `S`. -/
theorem isSheaf_quotBundleFunctor {S : Scheme.{u}} (E : S.Modules) (k : ℕ) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (quotBundleFunctor E k) :=
  Grassmannian.isSheaf_quotBundleFunctor E k

/-- On a trivializing affine chart `j : Spec R ⟶ S`, the restriction of `Quot_k(E)` is
`Quot_k(O^n)` on schemes over `Spec R`. -/
def chartQuotIso {S : Scheme.{u}} {E : S.Modules} {n : ℕ} (c : Grassmannian.TrivializingChart E n)
    (k : ℕ) : (Over.map c.j).op ⋙ quotBundleFunctor E k ≅ Grassmannian.quotFunctor c.R k n :=
  c.quotIso k

/-- On a trivializing affine chart `j : Spec R ⟶ S`, the restriction of `Quot_k(E)` is represented
by the Grassmannian `schemeOver R k n`. -/
def chartRepresentableBy {S : Scheme.{u}} {E : S.Modules} {n : ℕ}
    (c : Grassmannian.TrivializingChart E n) (k : ℕ) :
    ((Over.map c.j).op ⋙ quotBundleFunctor E k).RepresentableBy
      (Grassmannian.schemeOver c.R k n) :=
  c.representableBy k

/-- Trivializing affine charts cover `S` when `E` is finite locally free of constant rank `n`. -/
theorem exists_trivializingChart {S : Scheme.{u}} {E : S.Modules} {n : ℕ} (h : SheafHasRank E n)
    (x : S) : ∃ c : Grassmannian.TrivializingChart E n, x ∈ Set.range c.j :=
  Grassmannian.exists_trivializingChart h x

/-- `Quot_k(E)` is representable. -/
theorem quotBundleFunctor_isRepresentable {S : Scheme.{u}} (E : S.Modules) (k n : ℕ)
    (h : SheafHasRank E n) :
    (quotBundleFunctor E k).IsRepresentable :=
  Grassmannian.quotBundleFunctor_isRepresentable E k n h

/-- `Gr(E, k)` classifies rank-`k` locally free quotients of `E`. -/
theorem existsUnique_isoUnder_pullbackOver_universal {S : Scheme.{u}} (E : S.Modules) (k n : ℕ)
    (h : SheafHasRank E n) {T : Over S}
    (P : Grassmannian.LocallyFreeQuotientOf (Scheme.Modules.overPullback E T) k) :
    ∃! g : T ⟶ Grassmannian.grassmannianBundle E k n h,
      Nonempty (Grassmannian.LocallyFreeQuotientOf.IsoUnder
        ((Grassmannian.universalBundleQuotientRep E k n h).pullbackOver g) P) :=
  Grassmannian.existsUnique_isoUnder_pullbackOver_universal E k n h P

/-- `P(E) = Gr(E, 1)` classifies rank-one locally free quotients of `E`,
through the universal quotient `E_{P(E)} ↠ O_{P(E)}(1)`. -/
theorem projectiveBundle_existsUnique {S : Scheme.{u}} (E : S.Modules) (n : ℕ)
    (h : SheafHasRank E n) {T : Over S}
    (P : Grassmannian.LocallyFreeQuotientOf (Scheme.Modules.overPullback E T) 1) :
    ∃! g : T ⟶ Grassmannian.projectiveBundle E n h,
      Nonempty (Grassmannian.LocallyFreeQuotientOf.IsoUnder
        ((Grassmannian.projectiveBundleUniversalQuotient E n h).pullbackOver g) P) :=
  Grassmannian.projectiveBundle_existsUnique E n h P

example {S : Scheme.{u}} (E : S.Modules) (n : ℕ)
    (h : SheafHasRank E n) :
    SheafHasRank (Grassmannian.projectiveBundleTwistingSheaf E n h) 1 :=
  Grassmannian.sheafHasRank_projectiveBundleTwistingSheaf E n h

/-- `P(E)` classifies epimorphisms `E_T ⟶ L` onto line bundles. -/
theorem projectiveBundle_existsUnique_lineBundle {S : Scheme.{u}} (E : S.Modules) (n : ℕ)
    (h : SheafHasRank E n) {T : Over S}
    {L : T.left.Modules} (π : Scheme.Modules.overPullback E T ⟶ L) [Epi π]
    (hL : Invertible.IsLocallyRankOne T.left L) :
    ∃! g : T ⟶ Grassmannian.projectiveBundle E n h,
      ∃ e : ((Grassmannian.projectiveBundleUniversalQuotient E n h).pullbackOver g).obj ≅ L,
        ((Grassmannian.projectiveBundleUniversalQuotient E n h).pullbackOver g).π ≫ e.hom =
          π :=
  Grassmannian.projectiveBundle_existsUnique_lineBundle E n h π hL

/-- `Gr(E, k)` is locally the Grassmannian of `O^n`. -/
def grassmannianBundlePullbackIso {S : Scheme.{u}} (E : S.Modules) (k n : ℕ)
    (h : SheafHasRank E n)
    (c : Grassmannian.TrivializingChart E n) :
    (Over.pullback c.j).obj (Grassmannian.grassmannianBundle E k n h) ≅
      Grassmannian.schemeOver c.R k n :=
  Grassmannian.grassmannianBundlePullbackIso E k n h c

/-- `Gr(E, k) ⟶ S` is quasi-compact and locally of finite type. -/
theorem grassmannianBundle_hom_finiteType {S : Scheme.{u}} (E : S.Modules) (k n : ℕ)
    (h : SheafHasRank E n) :
    QuasiCompact (Grassmannian.grassmannianBundle E k n h).hom ∧
      LocallyOfFiniteType (Grassmannian.grassmannianBundle E k n h).hom :=
  ⟨Grassmannian.quasiCompact_grassmannianBundle_hom E k n h,
    Grassmannian.locallyOfFiniteType_grassmannianBundle_hom E k n h⟩

/-- The free case: for `E = O^n` on `Spec R` and the identity chart, the restriction of
`Quot_k(E)` is F8's `Quot_k(O^n)`, Stacks' `G(n − k, n)` over `R`. -/
def freeChartQuotIso (R : CommRingCat.{u}) (k n : ℕ) :
    (Over.map (𝟙 (Spec R))).op ⋙ quotBundleFunctor (Grassmannian.freeSheaf (Spec R) n) k ≅
      Grassmannian.quotFunctor R k n :=
  (⟨R, 𝟙 _, inferInstance, pullbackFreeIso (𝟙 _) (ULift.{u} (Fin n))⟩ :
    Grassmannian.TrivializingChart (Grassmannian.freeSheaf (Spec R) n) n).quotIso k

/-- info: 'AglibTest.GrassmannianLocallyFree.quotBundleFunctor' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.quotBundleFunctor

/-- info: 'AglibTest.GrassmannianLocallyFree.isSheaf_quotBundleFunctor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.isSheaf_quotBundleFunctor

/-- info: 'AglibTest.GrassmannianLocallyFree.chartQuotIso' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.chartQuotIso

/-- info: 'AglibTest.GrassmannianLocallyFree.chartRepresentableBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.chartRepresentableBy

/-- info: 'AglibTest.GrassmannianLocallyFree.exists_trivializingChart' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.exists_trivializingChart

/-- info: 'AglibTest.GrassmannianLocallyFree.quotBundleFunctor_isRepresentable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.quotBundleFunctor_isRepresentable

/-- info: 'AglibTest.GrassmannianLocallyFree.existsUnique_isoUnder_pullbackOver_universal' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.existsUnique_isoUnder_pullbackOver_universal

/-- info: 'AglibTest.GrassmannianLocallyFree.projectiveBundle_existsUnique' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.projectiveBundle_existsUnique

/-- info: 'AglibTest.GrassmannianLocallyFree.projectiveBundle_existsUnique_lineBundle' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.projectiveBundle_existsUnique_lineBundle

/-- info: 'AglibTest.GrassmannianLocallyFree.freeChartQuotIso' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.freeChartQuotIso

/-- info: 'AglibTest.GrassmannianLocallyFree.grassmannianBundlePullbackIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.grassmannianBundlePullbackIso

/-- info: 'AglibTest.GrassmannianLocallyFree.grassmannianBundle_hom_finiteType' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianLocallyFree.grassmannianBundle_hom_finiteType


end AglibTest.GrassmannianLocallyFree
