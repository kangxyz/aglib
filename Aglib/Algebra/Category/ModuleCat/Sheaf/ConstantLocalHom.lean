/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.Algebra.Category.ModuleCat.Sheaf.FinitePresentationLifting

/-! # Morphisms of constant finite-presentation module sheaves are locally constant

The original sheafification units identify a constant module morphism on a
covering sieve. The local equation holds on every further restriction, and
therefore describes the original sheaf morphism, not only stalk cardinalities
or an abstract local fullness hypothesis. No connectedness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf

universe u v r

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type r} [Ring R]

attribute [local instance] hasSheafify

/-- The literal native constant-presheaf-to-sheaf map. -/
abbrev constantUnit (M : ModuleCat.{max u v} R) :
    (Functor.const Cᵒᵖ).obj M ⟶
      ((constantSheaf J (ModuleCat.{max u v} R)).obj M).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj M)

/-- Equality with one constant module map persists on all further restrictions. -/
theorem constantUnit_hom_naturality
    {M N : ModuleCat.{max u v} R}
    (φ : (constantSheaf J (ModuleCat.{max u v} R)).obj M ⟶
      (constantSheaf J (ModuleCat.{max u v} R)).obj N)
    {U V : C} (f : V ⟶ U) (a : M ⟶ N)
    (ha : (constantUnit J M).app (op U) ≫ φ.hom.app (op U) =
      a ≫ (constantUnit J N).app (op U)) :
    (constantUnit J M).app (op V) ≫ φ.hom.app (op V) =
      a ≫ (constantUnit J N).app (op V) := by
  have hM : (constantUnit J M).app (op V) =
      (constantUnit J M).app (op U) ≫
        ((constantSheaf J (ModuleCat.{max u v} R)).obj M).obj.map f.op := by
    simpa using (constantUnit J M).naturality f.op
  have hN : (constantUnit J N).app (op V) =
      (constantUnit J N).app (op U) ≫
        ((constantSheaf J (ModuleCat.{max u v} R)).obj N).obj.map f.op := by
    simpa using (constantUnit J N).naturality f.op
  calc
    (constantUnit J M).app (op V) ≫ φ.hom.app (op V) =
        (constantUnit J M).app (op U) ≫
          ((constantSheaf J (ModuleCat.{max u v} R)).obj M).obj.map f.op ≫
            φ.hom.app (op V) := by rw [hM, Category.assoc]
    _ = (constantUnit J M).app (op U) ≫ φ.hom.app (op U) ≫
        ((constantSheaf J (ModuleCat.{max u v} R)).obj N).obj.map f.op := by
      rw [φ.hom.naturality f.op]
    _ = a ≫ (constantUnit J N).app (op V) := by
      rw [← Category.assoc, ha, Category.assoc, ← hN]

/-- A sieve of charts where the original sheaf morphism comes from an actual
module map, expressed through the original sheafification units. -/
def constantMapSieve {M N : ModuleCat.{max u v} R}
    (φ : (constantSheaf J (ModuleCat.{max u v} R)).obj M ⟶
      (constantSheaf J (ModuleCat.{max u v} R)).obj N) (U : C) : Sieve U where
  arrows V _ := ∃ a : M ⟶ N,
    (constantUnit J M).app (op V) ≫ φ.hom.app (op V) =
      a ≫ (constantUnit J N).app (op V)
  downward_closed := by
    rintro V W f ⟨a, ha⟩ g
    exact ⟨a, constantUnit_hom_naturality J φ g a ha⟩

/-- A map from a constant finitely presented module to any constant module
is genuinely constant on a covering sieve of every test object. -/
theorem constantMapSieve_mem {M N : ModuleCat.{max u v} R}
    [Module.FinitePresentation R M]
    (φ : (constantSheaf J (ModuleCat.{max u v} R)).obj M ⟶
      (constantSheaf J (ModuleCat.{max u v} R)).obj N) (U : C) :
    constantMapSieve J φ U ∈ J U := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max u v} R)) :=
    forget_preservesFilteredColimits R
  let : J.PreservesSheafification (forget (ModuleCat.{max u v} R)) :=
    GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{max u v} R))
  let η := constantUnit J N
  let : CategoryTheory.Presheaf.IsLocallySurjective J η :=
    CategoryTheory.Presheaf.isLocallySurjective_toSheafify' J
      (D := ModuleCat.{max u v} R) ((Functor.const Cᵒᵖ).obj N)
  let : CategoryTheory.Presheaf.IsLocallyInjective J η :=
    CategoryTheory.Presheaf.isLocallyInjective_toSheafify' J
      (D := ModuleCat.{max u v} R) ((Functor.const Cᵒᵖ).obj N)
  let := ModuleCat.Presheaf.locallySurjective_coyoneda_of_finitePresentation J η M
  let g : M ⟶ ((constantSheaf J (ModuleCat.{max u v} R)).obj N).obj.obj (op U) :=
    (constantUnit J M).app (op U) ≫ φ.hom.app (op U)
  refine J.superset_covering ?_
    (CategoryTheory.Presheaf.imageSieve_mem J
      (Functor.whiskerRight η (coyoneda.obj (op M))) g)
  intro V f hf
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, ?_⟩
  change a ≫ (constantUnit J N).app (op V) =
    (constantUnit J M).app (op U) ≫ φ.hom.app (op U) ≫
      ((constantSheaf J (ModuleCat.{max u v} R)).obj N).obj.map f.op at ha
  rw [← φ.hom.naturality f.op, ← Category.assoc,
    ← (constantUnit J M).naturality f.op] at ha
  change a ≫ (constantUnit J N).app (op V) =
    (𝟙 M ≫ (constantUnit J M).app (op V)) ≫ φ.hom.app (op V) at ha
  simpa only [Category.id_comp] using ha.symm

/-- For a Noetherian coefficient ring, finite generation of the source already
provides the finite relations needed for local constancy of morphisms. -/
theorem constantMapSieve_mem_of_finite [IsNoetherianRing R]
    {M N : ModuleCat.{max u v} R} [Module.Finite R M]
    (φ : (constantSheaf J (ModuleCat.{max u v} R)).obj M ⟶
      (constantSheaf J (ModuleCat.{max u v} R)).obj N) (U : C) :
    constantMapSieve J φ U ∈ J U := by
  let := Module.finitePresentation_of_finite R M
  exact constantMapSieve_mem J φ U

end ModuleCat.Sheaf
