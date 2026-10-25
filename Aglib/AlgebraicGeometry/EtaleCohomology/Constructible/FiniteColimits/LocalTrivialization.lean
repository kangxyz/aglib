/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Mathlib.Data.Fintype.EquivFin

/-! # Common actual etale charts for finite coefficient families

For a finite family of finite locally constant original coefficients, each
point admits one actual etale chart trivializing the whole object family.
The construction uses successive pullbacks of the supplied charts. It
does not assert that the coefficient arrows become constant on that chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits

universe u v

attribute [local instance] hasSheafifyLarge

/-- A single actual etale chart with finite constant trivializations of the
whole original coefficient family. -/
structure EtaleFamilyTrivialization {X : Scheme.{u}} {ι : Type v}
    (F : ι → AbelianSheaf.{u, u + 1} X) where
  /-- The etale chart over `X` used to trivialize every member of the original family `F`. -/
  chart : X.Etale
  /-- For each `i`, the finite abelian group giving the constant value of `F i` after pullback
  along `chart.hom`. -/
  value : ι → AddCommGrpCat.{u + 1}
  finite_value : ∀ i, Finite (value i)
  /-- For each `i`, the isomorphism from the pullback of `F i` along `chart.hom` to the constant
  sheaf with value `value i` on the small etale site of `chart.left`. -/
  trivialization : ∀ i, (inverseImage chart.hom).obj (F i) ≅
    (constantSheaf chart.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (value i)

/-- Successive actual chart pullbacks trivialize a finite sequence at an
original point, including the empty sequence. -/
theorem exists_etaleFamilyTrivialization_fin {X : Scheme.{u}} (r : ℕ)
    (F : Fin r → AbelianSheaf.{u, u + 1} X)
    (hF : ∀ i, IsFiniteLocallyConstant (F i)) (x : X) :
    ∃ t : EtaleFamilyTrivialization F, ∃ y : t.chart.left, t.chart.hom y = x := by
  induction r with
  | zero =>
    exact ⟨{
      chart := etaleTerminal X
      value := fun i => Fin.elim0 i
      finite_value := fun i => Fin.elim0 i
      trivialization := fun i => Fin.elim0 i }, x, rfl⟩
  | succ r ih =>
    obtain ⟨t, y, hy⟩ := ih (fun i => F i.succ) (fun i => hF i.succ)
    obtain ⟨s⟩ := isFiniteLocallyConstant_pullback t.chart.hom (hF 0)
    obtain ⟨j, z, hz⟩ := s.covers y
    let p := (s.chart j).hom ≫ t.chart.hom
    refine ⟨{
      chart := Scheme.Etale.mk p
      value := Fin.cases (s.value j) (fun i => t.value i)
      finite_value := ?_
      trivialization := ?_ }, z, ?_⟩
    · intro i
      exact Fin.cases (s.finite_value j) (fun i => t.finite_value i) i
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact (inverseImageComp t.chart.hom (s.chart j).hom).app (F 0) ≪≫
          s.trivialization j
      · exact (inverseImageComp t.chart.hom (s.chart j).hom).app (F k.succ) ≪≫
          (inverseImage (s.chart j).hom).mapIso (t.trivialization k) ≪≫
          (inverseImageConstantIso (s.chart j).hom).app (t.value k)
    · change t.chart.hom ((s.chart j).hom z) = x
      rw [hz, hy]

/-- An arbitrary finite object family has a common actual etale chart at
each original point. The coefficient and value universes are unchanged. -/
theorem exists_etaleFamilyTrivialization {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (F : ι → AbelianSheaf.{u, u + 1} X)
    (hF : ∀ i, IsFiniteLocallyConstant (F i)) (x : X) :
    ∃ t : EtaleFamilyTrivialization F, ∃ y : t.chart.left, t.chart.hom y = x := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  obtain ⟨t, y, hy⟩ := exists_etaleFamilyTrivialization_fin (Fintype.card ι)
    (fun i => F (e.symm i)) (fun i => hF (e.symm i)) x
  refine ⟨{
    chart := t.chart
    value := fun i => t.value (e i)
    finite_value := fun i => t.finite_value (e i)
    trivialization := fun i => ?_ }, y, hy⟩
  exact eqToIso (congrArg (fun G => (inverseImage t.chart.hom).obj G)
    (congrArg F (e.symm_apply_apply i).symm)) ≪≫ t.trivialization (e i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits
