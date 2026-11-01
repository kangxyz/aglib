/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology

/-!
# The original Künneth map with an affine second factor

Affine acyclicity reduces the native finite antidiagonal to its original
(n,0) summand. The resulting equation concerns the already defined Künneth
map and external tensor map. Their invertibility still requires the actual
flat-base-change comparison, rather than an assumed Künneth isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem directSum_lof_bijective_of_subsingleton
    {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (i₀ : ι) (hM : ∀ i, i ≠ i₀ → Subsingleton (M i)) :
    Function.Bijective (DirectSum.lof R ι M i₀) := by
  refine ⟨DirectSum.of_injective i₀, ?_⟩
  intro z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of i x =>
    by_cases hi : i = i₀
    · subst i
      exact ⟨x, rfl⟩
    · let := hM i hi
      refine ⟨0, ?_⟩
      rw [map_zero, Subsingleton.elim x 0, map_zero]
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k) [IsAffine Y.left]

/-- Affine acyclicity makes the original (n,0) antidiagonal inclusion bijective. -/
theorem structureKunnethSum_lof_bijective_of_isAffine (n : ℕ) :
    Function.Bijective (DirectSum.lof k _
      (fun s : HomologicalComplex₂.TotalDegree n =>
        structureCohomology k X s.val.1 ⊗[k] structureCohomology k Y s.val.2)
      (⟨(n, 0), Nat.add_zero n⟩ : HomologicalComplex₂.TotalDegree n)) := by
  classical
  apply directSum_lof_bijective_of_subsingleton
  intro s hs
  have hq : s.val.2 ≠ 0 := by
    intro hq
    apply hs
    apply Subtype.ext
    apply Prod.ext
    · change s.val.1 = n
      have h := s.property
      change s.val.1 + s.val.2 = n at h
      omega
    · exact hq
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hq
  have : Subsingleton (structureCohomology k Y s.val.2) := by
    rw [hq]
    exact structureCohomology_subsingleton_of_isAffine Y q
  infer_instance

/-- The canonical affine reduction uses exactly the original antidiagonal inclusion. -/
def structureKunnethSumAffineEquiv (n : ℕ) :
    structureCohomology k X n ⊗[k] structureCohomology k Y 0 ≃ₗ[k]
      structureKunnethSum X Y n :=
  LinearEquiv.ofBijective
    (DirectSum.lof k _ _ (⟨(n, 0), Nat.add_zero n⟩ : HomologicalComplex₂.TotalDegree n))
    (structureKunnethSum_lof_bijective_of_isAffine X Y n)

/-- The original finite-antidiagonal map reduces to the original degree-(n,0) tensor map. -/
theorem structureKunnethMap_affine_equiv (n : ℕ) :
    structureKunnethMap X Y n ∘ₗ (structureKunnethSumAffineEquiv X Y n).toLinearMap =
      structureExternalTensor X Y (Nat.add_zero n) := by
  apply LinearMap.ext
  intro z
  exact structureKunnethMap_lof X Y n ⟨(n, 0), Nat.add_zero n⟩ z

/-- For an affine second factor, bijectivity is precisely that of the actual
remaining tensor map; this reduction does not assume or assert its base-change proof. -/
theorem structureKunnethMap_bijective_iff_of_isAffine (n : ℕ) :
    Function.Bijective (structureKunnethMap X Y n) ↔
      Function.Bijective (structureExternalTensor X Y (Nat.add_zero n)) := by
  have h := structureKunnethMap_affine_equiv X Y n
  have he := (structureKunnethSumAffineEquiv X Y n).bijective
  constructor
  · intro hb
    rw [← h]
    exact hb.comp he
  · intro hb
    apply (Function.Bijective.of_comp_iff (structureKunnethMap X Y n) he).mp
    change Function.Bijective
      (structureKunnethMap X Y n ∘ₗ (structureKunnethSumAffineEquiv X Y n).toLinearMap)
    rw [h]
    exact hb

end AlgebraicGeometry.Scheme.Cohomology
