/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant

/-! # Etale locality of finite-type locally constant module coefficients

Composing actual jointly surjective etale covers and their actual constant
module trivializations proves the locality assertion. The covering families
need not be finite, and no global constant-functor fullness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Composition of genuine module trivializations on an etale covering family. -/
def finiteTypeLocalTrivializationOfCover {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale)
    (hU : ∀ x : X, ∃ i, ∃ y : (U i).left, (U i).hom y = x)
    (F : ModuleSheaf R X)
    (t : ∀ i, FiniteTypeLocalTrivialization ((moduleInverseImage R (U i).hom).obj F)) :
    FiniteTypeLocalTrivialization F where
  index := Σ i, (t i).index
  chart a := Scheme.Etale.mk (((t a.1).chart a.2).hom ≫ (U a.1).hom)
  covers x := by
    obtain ⟨i, y, hy⟩ := hU x
    obtain ⟨j, z, hz⟩ := (t i).covers y
    refine ⟨⟨i, j⟩, z, ?_⟩
    change (U i).hom (((t i).chart j).hom z) = x
    rw [hz, hy]
  value a := (t a.1).value a.2
  finite_value a := (t a.1).finite_value a.2
  trivialization a :=
    (moduleInverseImageComp R (U a.1).hom ((t a.1).chart a.2).hom).app F ≪≫
      (t a.1).trivialization a.2

/-- Finite-type local constancy can be checked on any jointly surjective
family of actual etale charts. -/
theorem isFiniteTypeLocallyConstant_of_etaleCover {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Etale)
    (hU : ∀ x : X, ∃ i, ∃ y : (U i).left, (U i).hom y = x)
    (F : ModuleSheaf R X)
    (hF : ∀ i, IsFiniteTypeLocallyConstant ((moduleInverseImage R (U i).hom).obj F)) :
    IsFiniteTypeLocallyConstant F :=
  ⟨finiteTypeLocalTrivializationOfCover U hU F (fun i => (hF i).some)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
