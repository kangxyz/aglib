/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.Etale
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Regularity descent for essentially etale local maps

For the same actual local algebra map, flatness identifies the extension of
the maximal ideal with its tensor product. Passing to residue fields preserves
its minimal number of generators. Formal unramifiedness and essential finite
type identify the extended ideal with the target maximal ideal, and the
dimension equality from `RegularLocalRing.Etale` then proves regularity descent.
-/

@[expose] public noncomputable section

open IsLocalRing TensorProduct

namespace Algebra.FormallyUnramified

section IdealBaseChange

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

private def idealTensorMap (I : Ideal R) :
    S ⊗[R] I →ₗ[S] I.map (algebraMap R S) :=
  (Algebra.idealMap S I).liftBaseChange S

private lemma idealTensorMap_surjective (I : Ideal R) :
    Function.Surjective (idealTensorMap (S := S) I) := by
  suffices h : ∀ x ∈ I.map (algebraMap R S),
      ∃ y, (idealTensorMap (S := S) I y : S) = x by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := h x hx
    exact ⟨y, Subtype.ext hy⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨1 ⊗ₜ[R] (⟨r, hr⟩ : I), by simp [idealTensorMap]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul s x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨s • a, by simp [ha]⟩

private def idealTensorEquiv [Module.Flat R S] (I : Ideal R) :
    S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) := by
  apply LinearEquiv.ofBijective (idealTensorMap I)
  refine ⟨?_, idealTensorMap_surjective I⟩
  have hcomp : (I.map (algebraMap R S)).subtype ∘ₗ idealTensorMap I =
      (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor S S I.subtype := by
    apply AlgebraTensorModule.ext
    intro s x
    simp [idealTensorMap, Algebra.smul_def, mul_comm]
  have hinj : Function.Injective
      (AlgebraTensorModule.lTensor S S I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective
  have h : Function.Injective
      ((I.map (algebraMap R S)).subtype ∘ₗ idealTensorMap (S := S) I) := by
    rw [hcomp]
    exact (AlgebraTensorModule.rid R S S).injective.comp hinj
  intro x y hxy
  apply h
  exact congrArg Subtype.val hxy

end IdealBaseChange

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [EssFiniteType R S]
    [Module.Flat R S] [FormallyUnramified R S]

/-- An essentially finite type, flat, formally unramified local map preserves
the minimal number of generators of the maximal ideal. -/
theorem spanFinrank_maximalIdeal_eq_of_flat :
    (maximalIdeal S).spanFinrank = (maximalIdeal R).spanFinrank := by
  let e : S ⊗[R] maximalIdeal R ≃ₗ[S] maximalIdeal S :=
    (idealTensorEquiv (maximalIdeal R)).trans
      (LinearEquiv.ofEq _ _ (map_maximalIdeal (R := R) (S := S)))
  let eS := e.baseChange S (ResidueField S) _ _
  let cS := AlgebraTensorModule.cancelBaseChange
    R S (ResidueField S) (ResidueField S) (maximalIdeal R)
  let cR := AlgebraTensorModule.cancelBaseChange
    R (ResidueField R) (ResidueField S) (ResidueField S) (maximalIdeal R)
  calc
    (maximalIdeal S).spanFinrank =
        Module.finrank (ResidueField S)
          (ResidueField S ⊗[S] maximalIdeal S) := by
      rw [← TensorProduct.spanFinrank_top_eq_of_residueField
        (maximalIdeal S) (maximalIdeal S).fg_of_isNoetherianRing,
        Module.finrank_eq_spanFinrank_of_free]
    _ = Module.finrank (ResidueField S)
        (ResidueField S ⊗[S] (S ⊗[R] maximalIdeal R)) := eS.finrank_eq.symm
    _ = Module.finrank (ResidueField S)
        (ResidueField S ⊗[R] maximalIdeal R) := cS.finrank_eq
    _ = Module.finrank (ResidueField S)
        (ResidueField S ⊗[ResidueField R]
          (ResidueField R ⊗[R] maximalIdeal R)) := cR.finrank_eq.symm
    _ = Module.finrank (ResidueField R)
        (ResidueField R ⊗[R] maximalIdeal R) := Module.finrank_baseChange
    _ = (maximalIdeal R).spanFinrank := by
      rw [Module.finrank_eq_spanFinrank_of_free,
        TensorProduct.spanFinrank_top_eq_of_residueField
          (maximalIdeal R) (maximalIdeal R).fg_of_isNoetherianRing]

/-- Embedding dimensions are equal for the same essentially etale local map. -/
theorem finrank_cotangentSpace_eq_of_flat :
    Module.finrank (ResidueField S) (CotangentSpace S) =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact spanFinrank_maximalIdeal_eq_of_flat R S

omit [IsLocalRing S] [IsNoetherianRing S] in
/-- Regularity descends along an essentially finite type, flat, formally
unramified local algebra map. -/
theorem isRegularLocalRing_base_of_flat [IsRegularLocalRing S] : IsRegularLocalRing R := by
  apply (isRegularLocalRing_iff R).mpr
  rw [← spanFinrank_maximalIdeal_eq_of_flat R S, ← ringKrullDim_eq_of_flat R S]
  exact IsRegularLocalRing.spanFinrank_maximalIdeal

/-- Regularity is equivalent on the two sides of an essentially etale local map. -/
theorem isRegularLocalRing_iff_of_flat : IsRegularLocalRing R ↔ IsRegularLocalRing S := by
  constructor
  · intro h
    let := h
    exact isRegularLocalRing_of_flat R S
  · intro h
    let := h
    exact isRegularLocalRing_base_of_flat R S

end Algebra.FormallyUnramified
