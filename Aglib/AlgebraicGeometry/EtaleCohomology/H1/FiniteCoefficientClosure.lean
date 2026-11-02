/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback
public import Aglib.CategoryTheory.Sites.Pullback.FiniteProducts

/-! # Finite powers of the original finite local trivializations

The same charts, covering witnesses and finite values are retained.
Product comparison and product finiteness use the shared pure API.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge Fintype.ofFinite

/-- Compose the original trivializing charts with the same surjective
etale map, retaining values and the original composition comparison. -/
theorem isFiniteLocallyConstant_of_etale_pullback
    {X Y : Scheme.{u}} (p : Y ⟶ X) [Etale p] (hp : Function.Surjective p)
    (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsFiniteLocallyConstant ((inverseImage p).obj F)) :
    IsFiniteLocallyConstant F := by
  obtain ⟨t⟩ := hF
  refine ⟨{
    index := t.index
    chart := fun i => Scheme.Etale.mk ((t.chart i).hom ≫ p)
    covers := ?_
    value := t.value
    finite_value := t.finite_value
    trivialization := fun i =>
      (inverseImageComp p (t.chart i).hom).app F ≪≫ t.trivialization i }⟩
  intro x
  obtain ⟨y, rfl⟩ := hp x
  obtain ⟨i, z, hz⟩ := t.covers y
  exact ⟨i, z, by change p ((t.chart i).hom z) = p y; rw [hz]⟩

/-- The same actual charts trivialize the actual finite product; all
categorical comparison factors come from the shared pure constructor. -/
def FiniteLocalTrivialization.finitePower {X : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (t : FiniteLocalTrivialization F)
    (I : Type u) [Finite I] : FiniteLocalTrivialization (∏ᶜ fun _ : I => F) where
  index := t.index
  chart := t.chart
  covers := t.covers
  value j := ∏ᶜ fun _ : I => t.value j
  finite_value j := by
    let := t.finite_value j
    exact AddCommGrpCat.finite_power_value I (t.value j)
  trivialization j :=
    Functor.powerTrivializationIso (inverseImage (t.chart j).hom)
      (constantSheaf (Scheme.smallEtaleTopology (t.chart j).left) AddCommGrpCat.{u + 1})
      (t.trivialization j) I

/-- The original finite local constancy property is closed under these
finite powers, without a replacement representation. -/
theorem isFiniteLocallyConstant_finitePower {X : Scheme.{u}}
    {F : AbelianSheaf.{u, u + 1} X} (I : Type u) [Finite I]
    (hF : IsFiniteLocallyConstant F) : IsFiniteLocallyConstant (∏ᶜ fun _ : I => F) := by
  obtain ⟨t⟩ := hF
  exact ⟨t.finitePower I⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
