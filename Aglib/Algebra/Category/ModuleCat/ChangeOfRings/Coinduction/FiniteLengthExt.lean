/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Projective
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthExtDuality

/-!
# Original target-ring scalars detected by coinduced Ext-two

The original coinduction Ext comparison and the proved finite-length
R-Ext-two faithfulness identify the scalars annihilating a finite-length
restricted A-module and its actual A-Ext-two group with coefficient Hom_R(A,R).
This module-level statement uses neither a derived biduality premise nor
an injective-hull identification. The geometric trace comparison remains separate.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace ModuleCat

variable {R A : Type u} [CommRing R] [CommRing A] [IsRegularLocalRing R]
  (σ : R →+* A)
  [Module.Projective R ((restrictScalars σ).obj (ModuleCat.of A A))]

/-- Scalar annihilation of the original A-module is equivalent to scalar
annihilation of its actual A-Ext-two into the native coinduced ring module. -/
theorem coinducedExtTwo_scalar_annihilates_iff
    (hR : ringKrullDim R = (2 : ℕ)) (M : ModuleCat.{u} A)
    (hM : IsFiniteLength R ((restrictScalars σ).obj M)) (a : A) :
    (∀ x : Ext M ((coextendScalars σ).obj (ModuleCat.of R R)) 2, a • x = 0) ↔
      ∀ m : M, a • m = 0 := by
  let E := coextendScalarsExtEquiv σ M (ModuleCat.of R R) 2
  let f : (restrictScalars σ).obj M ⟶ (restrictScalars σ).obj M :=
    (restrictScalars σ).map (a • 𝟙 M)
  constructor
  · intro h
    have hD : IsRegularLocalRing.extDualTwoMap R f = 0 := by
      apply LinearMap.ext
      intro x
      apply E.injective
      change E ((Ext.mk₀ f).comp x (zero_add 2)) = E 0
      rw [map_zero]
      change coextendScalarsExtEquiv σ M (ModuleCat.of R R) 2
          ((Ext.mk₀ ((restrictScalars σ).map (a • 𝟙 M))).comp x (zero_add 2)) = 0
      rw [coextendScalarsExtEquiv_source_smul]
      exact h _
    have hf : f = 0 :=
      (IsRegularLocalRing.extDualTwoMap_eq_zero_iff R hR f hM hM).mp hD
    intro m
    have hm := ConcreteCategory.congr_hom hf m
    exact hm
  · intro h
    have hmul : a • 𝟙 M = (0 : M ⟶ M) := by
      apply ConcreteCategory.hom_ext
      exact h
    have hf : f = 0 := by
      dsimp [f]
      rw [hmul, Functor.map_zero]
    intro x
    obtain ⟨y, rfl⟩ := E.surjective x
    change a • coextendScalarsExtEquiv σ M (ModuleCat.of R R) 2 y = 0
    rw [← coextendScalarsExtEquiv_source_smul]
    change E ((Ext.mk₀ f).comp y (zero_add 2)) = 0
    rw [hf, Ext.mk₀_zero, Ext.zero_comp, map_zero]

/-- The annihilator ideal for the intrinsic A-action on coinduced Ext-two
is exactly the annihilator ideal of the original A-module. -/
theorem coinducedExtTwo_annihilator
    (hR : ringKrullDim R = (2 : ℕ)) (M : ModuleCat.{u} A)
    (hM : IsFiniteLength R ((restrictScalars σ).obj M)) :
    Module.annihilator A (Ext M ((coextendScalars σ).obj (ModuleCat.of R R)) 2) =
      Module.annihilator A M := by
  ext a
  simp only [Module.mem_annihilator]
  exact coinducedExtTwo_scalar_annihilates_iff σ hR M hM a

end ModuleCat
