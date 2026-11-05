/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConstantSectionZeroClosed
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant

/-! # Closed zero loci of finite-type locally constant module sections

The same original zero open pulls back along the actual trivializing charts.
Its closedness follows from the constant case and descent along open jointly
surjective charts. The additive carrier need not be finite or torsion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

variable (R : Type r) [Ring R]

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- The original underlying section zero open is closed for every native
finite-type local system over an arbitrary ring. -/
theorem isClosed_sectionZeroOpen_of_isFiniteTypeLocallyConstant
    {X : Scheme.{u}} (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F)
    (a : (globalSections X).obj ((moduleUnderlying R X).obj F)) :
    IsClosed (sectionZeroOpen ((moduleUnderlying R X).obj F) a : Set X) := by
  obtain ⟨t⟩ := hF
  let G := (moduleUnderlying R X).obj F
  let Z := sectionZeroOpen G a
  have hc (i : t.index) : IsClosed ((t.chart i).hom ⁻¹' (Z : Set X)) := by
    let j : (t.chart i).left ⟶ X := (t.chart i).hom
    let e : (inverseImage j).obj G ≅
        (constantSheaf (t.chart i).left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj (t.value i)) :=
      ((moduleInverseImageUnderlyingIso R j).app F).symm ≪≫
        (moduleUnderlying R (t.chart i).left).mapIso (t.trivialization i) ≪≫
        (moduleConstantUnderlyingIso R (t.chart i).left).app (t.value i)
    have hz := isClosed_sectionZeroOpen_constant (t.chart i).left
      ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj (t.value i))
      ((globalSections (t.chart i).left).map e.hom (globalSectionsPullback j G a))
    have hz' : IsClosed (sectionZeroOpen ((inverseImage j).obj G)
        (globalSectionsPullback j G a) : Set (t.chart i).left) :=
      (sectionZeroOpen_mapIso e (globalSectionsPullback j G a)) ▸ hz
    rw [sectionZeroOpen_globalSectionsPullback] at hz'
    exact hz'
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨i, y, hy⟩ := t.covers x
  have hO : IsOpen ((t.chart i).hom '' ((t.chart i).hom ⁻¹' (Z : Set X))ᶜ) :=
    (t.chart i).hom.isOpenMap _ (hc i).isOpen_compl
  apply Filter.mem_of_superset (hO.mem_nhds ?_) ?_
  · exact ⟨y, by simpa only [Set.mem_compl_iff, Set.mem_preimage, hy] using hx, hy⟩
  · rintro z ⟨w, hw, rfl⟩
    exact hw

/-- Dominant inverse image detects original sections whenever their actual
zero opens are closed. This is independent of coefficient finiteness. -/
theorem globalSectionsPullback_injective_of_closedZeroLoci
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsDominant f]
    (G : AbelianSheaf.{u, u + 1} X)
    (hG : ∀ a : (globalSections X).obj G,
      IsClosed (sectionZeroOpen G a : Set X)) :
    Function.Injective (globalSectionsPullback f G) := by
  have hz (a : (globalSections X).obj G) (ha : globalSectionsPullback f G a = 0) : a = 0 := by
    apply (sectionZeroOpen_eq_top_iff G a).mp
    have hp : sectionZeroOpen ((inverseImage f).obj G)
        (globalSectionsPullback f G a) = ⊤ :=
      (sectionZeroOpen_eq_top_iff _ _).mpr ha
    rw [sectionZeroOpen_globalSectionsPullback] at hp
    have hr : Set.range f ⊆ (sectionZeroOpen G a : Set X) := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ f ⁻¹ᵁ sectionZeroOpen G a := by rw [hp]; trivial
      exact hy
    have ht : (Set.univ : Set X) ⊆ (sectionZeroOpen G a : Set X) := by
      rw [← f.denseRange.closure_range]
      exact closure_minimal hr (hG a)
    ext x
    exact ⟨fun _ => trivial, fun _ => ht (Set.mem_univ x)⟩
  intro a b hab
  apply sub_eq_zero.mp
  exact hz (a - b) (by simp only [map_sub, hab, sub_self])

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
