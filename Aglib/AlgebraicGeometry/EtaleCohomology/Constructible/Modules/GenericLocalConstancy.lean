/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Finite-type local constancy on a dense affine open

For a constructible native module sheaf on an integral scheme, the actual
stratum through the generic point of an affine open is an open subscheme.
Indeed, its closed factor in the immersion factorization is dominant and
therefore surjective, hence an isomorphism onto the reduced open target.
An affine refinement retains finite-type local constancy through the original
module inverse-image composition. No Noetherian or coefficient finiteness
hypothesis is used. The curve dimension argument consumes this supplier.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Constructible module coefficients on an integral scheme are finite-type
locally constant on an actual dense affine open, with their original restriction. -/
theorem exists_dense_affine_open_isFiniteTypeLocallyConstant
    {X : Scheme.{u}} [IsIntegral X] (F : ModuleSheaf R X) (hF : IsConstructible F) :
    ∃ (U : Scheme.{u}) (j : U ⟶ X), IsAffine U ∧ IsOpenImmersion j ∧
      IsDominant j ∧ IsIntegral U ∧
        IsFiniteTypeLocallyConstant ((moduleInverseImage R j).obj F) := by
  obtain ⟨W, hW, hηW, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := genericPoint X) (U := ⊤) (by simp)
  have : Nonempty W.toScheme := ⟨⟨genericPoint X, hηW⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  obtain ⟨p⟩ := hF ⟨W, hW⟩
  obtain ⟨i, z, hz⟩ := p.covers (genericPoint W.toScheme)
  let c := p.inclusion i
  have : IsImmersion c := p.immersion i
  have : IsDominant c := by
    constructor
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
      ← (genericPoint_spec W.toScheme).def]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨z, hz⟩)
  have : IsDominant (c.liftCoborder ≫ c.coborderRange.ι) := by
    rw [c.liftCoborder_ι]
    infer_instance
  have : IsDominant c.liftCoborder :=
    IsDominant.of_comp_of_isOpenImmersion c.liftCoborder c.coborderRange.ι
  have : Surjective c.liftCoborder :=
    surjective_of_isDominant_of_isClosed_range c.liftCoborder
      c.liftCoborder.isClosedEmbedding.isClosed_range
  have : IsIso c.liftCoborder := isIso_of_isClosedImmersion_of_surjective c.liftCoborder
  have : IsOpenImmersion c := by
    rw [← c.liftCoborder_ι]
    infer_instance
  have : Nonempty (p.stratum i) := ⟨z⟩
  have : IsIntegral (p.stratum i) := isIntegral_of_isOpenImmersion c
  obtain ⟨V, hV, hzV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := p.stratum i) (x := z) (U := ⊤) (by simp)
  have : Nonempty V.toScheme := ⟨⟨z, hzV⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let j : V.toScheme ⟶ X := (V.ι ≫ c) ≫ W.ι
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion ((V.ι ≫ c) ≫ W.ι))
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  refine ⟨V.toScheme, j, hV, inferInstance, inferInstance, inferInstance, ?_⟩
  let e := (moduleInverseImageComp R W.ι (V.ι ≫ c)).app F ≪≫
    (moduleInverseImageComp R c V.ι).app ((moduleInverseImage R W.ι).obj F)
  exact (isFiniteTypeLocallyConstant_iff_of_iso e).mpr
    (isFiniteTypeLocallyConstant_pullback V.ι (p.locally_constant i))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
