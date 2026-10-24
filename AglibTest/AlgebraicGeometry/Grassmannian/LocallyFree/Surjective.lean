/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Surjective

/-!
# Surjectivity of `Gr(E, k) ⟶ S`

The instance in `Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies the premise
`Module.Grassmannian.BaseChangeMkQFormula`. The examples below restate, with no further
hypothesis, that the free sheaf `O^k` has rank `k`, that the projection `O^k ⨿ O^m ⟶ O^k` is an
epimorphism and the coordinate projection `O^{k + m} ↠ O^k` a rank-`k` quotient, that
trivializing charts lift to `Gr(E, k)`, and that `Gr(E, k) ⟶ S` is surjective for `E` of constant
rank `n ≥ k`, in particular for the linear-system case `n = k + 1`. Each declaration is guarded
for the standard axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules

universe u

namespace AglibTest.GrassmannianSurjective

open AlgebraicGeometry.Grassmannian

/-- The free sheaf `O_X^k` has constant rank `k`. -/
example (X : Scheme.{u}) (k : ℕ) : SheafHasRank (freeSheaf X k) k :=
  sheafHasRank_freeSheaf X k

/-- The projection `O^k ⨿ O^m ⟶ O^k` onto the first summand is an epimorphism. -/
example (X : Scheme.{u}) (k m : ℕ) : Epi (coordinateProjectionMap X k m) :=
  inferInstance

/-- The coordinate projection is a quotient of `O^{k + m}` onto `O^k`. -/
example (X : Scheme.{u}) (k m : ℕ) :
    (LocallyFreeQuotient.coordinateProjection X k m).obj = freeSheaf X k :=
  LocallyFreeQuotient.coordinateProjection_obj X k m

/-- Every trivializing chart of `E` lifts to `Gr(E, k)` over `S`. -/
example {S : Scheme.{u}} (E : S.Modules) (k n : ℕ) (h : SheafHasRank E n) (hk : k ≤ n)
    (c : TrivializingChart E n) :
    ∃ g : Spec c.R ⟶ (grassmannianBundle E k n h).left,
      g ≫ (grassmannianBundle E k n h).hom = c.j :=
  exists_comp_grassmannianBundle_hom_eq_trivializingChart E k h hk c

/-- `Gr(E, k) ⟶ S` is surjective for `E` of constant rank `n ≥ k`. -/
example {S : Scheme.{u}} (E : S.Modules) (k n : ℕ) (h : SheafHasRank E n) (hk : k ≤ n) :
    Surjective (grassmannianBundle E k n h).hom :=
  surjective_grassmannianBundle_hom_of_le E k h hk

/-- The linear-system case: `Gr(E, k) ⟶ S` is surjective for `E` of constant rank `k + 1`. -/
example {S : Scheme.{u}} (E : S.Modules) (k : ℕ) (h : SheafHasRank E (k + 1)) :
    Surjective (grassmannianBundle E k (k + 1) h).hom :=
  surjective_grassmannianBundle_hom_of_le E k h (Nat.le_succ k)

/--
info: 'AlgebraicGeometry.Grassmannian.sheafHasRank_freeSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sheafHasRank_freeSheaf

/--
info: 'AlgebraicGeometry.Grassmannian.epi_coordinateProjectionMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms epi_coordinateProjectionMap

/--
info: 'AlgebraicGeometry.Grassmannian.LocallyFreeQuotient.coordinateProjection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocallyFreeQuotient.coordinateProjection

/--
info: 'AlgebraicGeometry.Grassmannian.exists_comp_grassmannianBundle_hom_eq_trivializingChart'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_comp_grassmannianBundle_hom_eq_trivializingChart

/--
info: 'AlgebraicGeometry.Grassmannian.surjective_grassmannianBundle_hom_of_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms surjective_grassmannianBundle_hom_of_le

end AglibTest.GrassmannianSurjective
