/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Stalk kernels of actual integral closed components

The proof follows the actual spectrum-of-stalk maps. The component generic
point has no strict generalization; injectivity of the canonical stalk-spectrum
map makes the actual stalk kernel a minimal prime. This supplies a generic
part of the special-fibre component-kernel obligation without a Noetherian,
flatness or arithmetic-trait condition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Hom

private lemma eq_genericPoint_of_specializes_component
    {T : Type*} [TopologicalSpace T] [T0Space T]
    {Z : Set T} {g x : T} (hg : IsGenericPoint g Z)
    (hZ : Z ∈ irreducibleComponents T) (h : x ⤳ g) : x = g := by
  have hsub : Z ⊆ closure {x} := by
    rw [← hg.def]
    exact specializes_iff_closure_subset.mp h
  have heq : IsGenericPoint x Z :=
    Set.Subset.antisymm (hZ.2 isIrreducible_singleton.closure hsub) hsub
  exact heq.eq hg

private lemma fromSpecStalk_bot {C : Scheme.{u}} [IsIntegral C] (c : C) :
    C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c)) = genericPoint C := by
  have hgB : IsGenericPoint (⊥ : PrimeSpectrum (C.presheaf.stalk c)) Set.univ := by
    rw [IsGenericPoint, PrimeSpectrum.closure_singleton]
    simp
  have hd : DenseRange (C.fromSpecStalk c) := by
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
    rw [← (genericPoint_spec C).def]
    apply closure_mono
    apply Set.singleton_subset_iff.mpr
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec C).specializes trivial
  have hg : IsGenericPoint
      (C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c))) Set.univ := by
    change closure {C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c))} = Set.univ
    calc
      closure {C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c))} =
          closure ((C.fromSpecStalk c) '' Set.univ) :=
        (hgB.image (C.fromSpecStalk c).continuous).def
      _ = closure (Set.range (C.fromSpecStalk c)) := by rw [Set.image_univ]
      _ = Set.univ := hd.closure_range
  exact hg.eq (genericPoint_spec C)

/-- An actual integral closed component has a minimal-prime stalk kernel at every point.
No Noetherianity or flatness hypothesis is required. -/
theorem ker_stalkMap_mem_minimalPrimes_of_irreducibleComponent
    {C Y : Scheme.{u}} [IsIntegral C] (i : C ⟶ Y) [IsClosedImmersion i]
    (hi : Set.range i ∈ irreducibleComponents Y) (c : C) :
    RingHom.ker (i.stalkMap c).hom ∈
      (⊥ : Ideal (Y.presheaf.stalk (i c))).minimalPrimes := by
  let p : PrimeSpectrum (Y.presheaf.stalk (i c)) :=
    PrimeSpectrum.comap (i.stalkMap c).hom (⊥ : PrimeSpectrum (C.presheaf.stalk c))
  have hg : IsGenericPoint (i (genericPoint C)) (Set.range i) := by
    simpa only [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] using
      (genericPoint_spec C).image i.continuous
  have hp : Y.fromSpecStalk (i c) p = i (genericPoint C) := by
    have h := congrArg
      (fun k : Spec (C.presheaf.stalk c) ⟶ Y =>
        k (⊥ : PrimeSpectrum (C.presheaf.stalk c)))
      (Scheme.SpecMap_stalkMap_fromSpecStalk i (x := c))
    change Y.fromSpecStalk (i c) p =
      i (C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c))) at h
    simpa only [fromSpecStalk_bot c] using h
  have hmin : IsMin p := by
    intro q hq
    have heq : q = p := by
      apply (Y.fromSpecStalk (i c)).isEmbedding.injective
      rw [hp]
      apply eq_genericPoint_of_specializes_component hg hi
      rw [← hp]
      exact ((PrimeSpectrum.le_iff_specializes q p).mp hq).map
        (Y.fromSpecStalk (i c)).continuous
    exact heq.ge
  exact (PrimeSpectrum.isMin_iff.mp hmin)

end AlgebraicGeometry.Scheme.Hom
