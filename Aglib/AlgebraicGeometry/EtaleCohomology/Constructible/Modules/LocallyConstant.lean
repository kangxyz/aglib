/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images
public import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Finite-type locally constant module coefficients

Local values are finitely generated modules, not finite additive groups. The
charts are actual jointly surjective etale charts and the trivializations are
isomorphisms of native ModuleCat-valued sheaves. Every scheme inverse image
preserves this property. Over a finite ring the same charts give original
finite locally constant abelian coefficients after forgetting scalars.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Actual etale local trivializations with finitely generated module values. -/
structure FiniteTypeLocalTrivialization {X : Scheme.{u}} (F : ModuleSheaf R X) where
  /-- The index type of the covering family; it need not be finite. -/
  index : Type u
  /-- The actual etale charts. -/
  chart : index → X.Etale
  /-- Joint surjectivity on the original underlying scheme. -/
  covers : ∀ x : X, ∃ i, ∃ y : (chart i).left, (chart i).hom y = x
  /-- The constant module value on each chart. -/
  value : index → ModuleCat.{u + 1} R
  /-- Finite generation over the original coefficient ring. -/
  finite_value : ∀ i, Module.Finite R (value i)
  /-- The actual module-valued local trivialization. -/
  trivialization : ∀ i, (moduleInverseImage R (chart i).hom).obj F ≅
    (constantSheaf (chart i).left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (value i)

/-- Local constancy with finite generation over the coefficient ring. -/
def IsFiniteTypeLocallyConstant {X : Scheme.{u}} (F : ModuleSheaf R X) : Prop :=
  Nonempty (FiniteTypeLocalTrivialization F)

/-- A module coefficient isomorphism retains the same charts and module values. -/
def FiniteTypeLocalTrivialization.ofIso {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (t : FiniteTypeLocalTrivialization F) (e : F ≅ G) : FiniteTypeLocalTrivialization G where
  index := t.index
  chart := t.chart
  covers := t.covers
  value := t.value
  finite_value := t.finite_value
  trivialization i := (moduleInverseImage R (t.chart i).hom).mapIso e.symm ≪≫ t.trivialization i

/-- Finite-type local constancy is invariant under actual module isomorphisms. -/
theorem isFiniteTypeLocallyConstant_iff_of_iso {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (e : F ≅ G) : IsFiniteTypeLocallyConstant F ↔ IsFiniteTypeLocallyConstant G :=
  ⟨fun ⟨t⟩ => ⟨t.ofIso e⟩, fun ⟨t⟩ => ⟨t.ofIso e.symm⟩⟩

/-- Base change of the original charts and module trivializations. -/
def FiniteTypeLocalTrivialization.pullback {X S : Scheme.{u}} {F : ModuleSheaf R X}
    (t : FiniteTypeLocalTrivialization F) (f : S ⟶ X) :
    FiniteTypeLocalTrivialization ((moduleInverseImage R f).obj F) where
  index := t.index
  chart i := Scheme.Etale.mk (pullback.snd (t.chart i).hom f)
  covers x := by
    obtain ⟨i, y, hy⟩ := t.covers (f x)
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨i, z, hz⟩
  value := t.value
  finite_value := t.finite_value
  trivialization i := by
    let a := (t.chart i).hom
    let g := pullback.fst a f
    let h := pullback.snd a f
    have square : h ≫ f = g ≫ a := pullback.condition.symm
    exact ((moduleInverseImageComp R f h).app F).symm ≪≫
      eqToIso (congrArg (fun q => (moduleInverseImage R q).obj F) square) ≪≫
      (moduleInverseImageComp R a g).app F ≪≫
      (moduleInverseImage R g).mapIso (t.trivialization i) ≪≫
      (moduleInverseImageConstantIso R g).app (t.value i)

/-- Every actual scheme inverse image preserves finite-type local constancy. -/
theorem isFiniteTypeLocallyConstant_pullback {X S : Scheme.{u}} (f : S ⟶ X)
    {F : ModuleSheaf R X} (hF : IsFiniteTypeLocallyConstant F) :
    IsFiniteTypeLocallyConstant ((moduleInverseImage R f).obj F) := by
  obtain ⟨t⟩ := hF
  exact ⟨t.pullback f⟩

/-- Finite-type constant modules have their actual identity-chart trivialization. -/
def finiteTypeConstantTrivialization (X : Scheme.{u}) (M : ModuleCat.{u + 1} R)
    [Module.Finite R M] :
    FiniteTypeLocalTrivialization
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) where
  index := PUnit.{u + 1}
  chart _ := etaleTerminal X
  covers x := ⟨PUnit.unit, x, rfl⟩
  value _ := M
  finite_value _ := inferInstance
  trivialization _ := (moduleInverseImageConstantIso R (𝟙 X)).app M

/-- Constant finite-type module coefficients are finite-type locally constant. -/
theorem isFiniteTypeLocallyConstant_constant (X : Scheme.{u}) (M : ModuleCat.{u + 1} R)
    [Module.Finite R M] :
    IsFiniteTypeLocallyConstant
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :=
  ⟨finiteTypeConstantTrivialization X M⟩

/-- Over a finite coefficient ring, the same actual charts become finite
abelian local trivializations through the original inverse-image comparison. -/
def FiniteTypeLocalTrivialization.underlying [Finite R] {X : Scheme.{u}}
    {F : ModuleSheaf R X} (t : FiniteTypeLocalTrivialization F) :
    FiniteLocalTrivialization ((moduleUnderlying R X).obj F) where
  index := t.index
  chart := t.chart
  covers := t.covers
  value i := (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj (t.value i)
  finite_value i := by
    change Finite (t.value i)
    let := t.finite_value i
    exact Module.finite_of_finite R
  trivialization i :=
    ((moduleInverseImageUnderlyingIso R (t.chart i).hom).app F).symm ≪≫
      (moduleUnderlying R (t.chart i).left).mapIso (t.trivialization i) ≪≫
      (moduleConstantUnderlyingIso R (t.chart i).left).app (t.value i)

/-- Finite-type local constancy over a finite ring implies original finite
abelian local constancy; no such assertion is made over an infinite ring. -/
theorem isFiniteLocallyConstant_underlying [Finite R] {X : Scheme.{u}}
    {F : ModuleSheaf R X} (hF : IsFiniteTypeLocallyConstant F) :
    IsFiniteLocallyConstant ((moduleUnderlying R X).obj F) := by
  obtain ⟨t⟩ := hF
  exact ⟨t.underlying⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
