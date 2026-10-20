/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.TensorProduct.FiniteData
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Smooth coefficient models carrying finite data

For an arbitrary commutative coefficient ring, the actual smooth algebra is
the stated scalar extension of a smooth model over a finitely generated
integer subalgebra. The canonical model map is injective and its image
contains the prescribed finite algebra and coefficient data. Universes and
the actual tensor equivalence are retained.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Smooth/FiniteModel.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`224517fcfb1a8866ec9f4f41dc6e6e131874f84ede9b359b0f631e61df6db3fd`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.TensorProduct

namespace Algebra.Smooth.FiniteModel

universe u v w

section SmoothData

variable {C : Type u} [CommRing C] {B : Type v} [CommRing B] [Algebra C B]

/-- The canonical model-ring map given by tensor inclusion followed by the
actual base-change equivalence. -/
def modelMap (A : Type*) [CommRing A] [Algebra A C]
    (D : Type*) [CommRing D] [Algebra A D]
    (e : C ⊗[A] D ≃ₐ[C] B) : D →+* B :=
  e.toRingHom.comp (Algebra.TensorProduct.includeRight : D →ₐ[A] C ⊗[A] D).toRingHom

/-- Flatness of the smooth model preserves the injective coefficient-ring map. -/
theorem modelMap_injective (A : Type*) [CommRing A] [Algebra A C] (D : Type*)
    [CommRing D] [Algebra A D] [Algebra.Smooth A D] (e : C ⊗[A] D ≃ₐ[C] B) :
    Function.Injective (algebraMap A C) → Function.Injective (modelMap A D e) := fun ha =>
  e.injective.comp (Algebra.TensorProduct.includeRight_injective
    (R := A) (A := C) (B := D) ha)

/-- Construct an actual smooth affine model over a finitely generated integer
subalgebra containing the given constants. Its injective canonical map lifts
every element of the prescribed finite ring data. -/
theorem exists_smooth_model_with_finite_data [Algebra.Smooth C B]
    (data : Finset B) (extra : Finset C) :
    ∃ (A : Subalgebra ℤ C) (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      A.FG ∧ Algebra.Smooth A D ∧ (∀ c ∈ extra, c ∈ A) ∧
      ∃ e : C ⊗[A] D ≃ₐ[C] B,
        Function.Injective (modelMap A D e) ∧
        ∀ b ∈ data, ∃ d : D, modelMap A D e d = b := by
  classical
  obtain ⟨A₀, D₀, iD₀, iAD₀, hA₀, hD₀, ⟨e₀⟩⟩ :=
    Algebra.Smooth.exists_subalgebra_fg ℤ C B
  let := iD₀
  let := iAD₀
  let := hD₀
  obtain ⟨S, hS, hextra, hlifts⟩ :=
    Algebra.TensorProduct.exists_fg_tensor_lifts (data.image e₀) extra
  have hFT : Algebra.FiniteType ℤ S :=
    Algebra.FiniteType.trans (A₀.fg_iff_finiteType.mp hA₀)
      (S.fg_iff_finiteType.mp hS)
  have hA : (S.restrictScalars ℤ).FG :=
    (S.restrictScalars ℤ).fg_iff_finiteType.mpr hFT
  let A := S.restrictScalars ℤ
  have hle : A₀ ≤ A := by
    intro c hc
    exact S.algebraMap_mem (⟨c, hc⟩ : A₀)
  let : Algebra A₀ A := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  let : IsScalarTower A₀ A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let D := A ⊗[A₀] D₀
  let j : S →ₐ[A₀] A := {
    toFun := fun s => ⟨s.val, s.property⟩
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }
  let e : C ⊗[A] D ≃ₐ[C] B :=
    (Algebra.TensorProduct.cancelBaseChange A₀ A C C D₀).trans e₀.symm
  have hmap (d : D) : modelMap A D e d =
      e₀.symm (Algebra.TensorProduct.rTensor D₀
        (IsScalarTower.toAlgHom A₀ A C) d) := by
    induction d using _root_.TensorProduct.inductionOn with
    | tmul s d =>
      change e₀.symm ((Algebra.TensorProduct.cancelBaseChange A₀ A C C D₀)
        (1 ⊗ₜ[A] (s ⊗ₜ[A₀] d))) = e₀.symm ((s : C) ⊗ₜ[A₀] d)
      apply congrArg e₀.symm
      have hs : algebraMap A C s = (s : C) := rfl
      simpa only [Algebra.smul_def, mul_one, hs] using
        (Algebra.TensorProduct.cancelBaseChange_tmul A₀ A C C D₀ (1 : C) s d)
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  have htransfer (y : S ⊗[A₀] D₀) :
      Algebra.TensorProduct.rTensor D₀ (IsScalarTower.toAlgHom A₀ A C)
        (Algebra.TensorProduct.rTensor D₀ j y) =
          Algebra.TensorProduct.rTensor D₀ S.val y := by
    induction y using _root_.TensorProduct.inductionOn with
    | tmul s d => simp [j]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨A, D, inferInstance, inferInstance, hA, inferInstance, hextra, e,
    modelMap_injective A D e Subtype.val_injective, ?_⟩
  intro b hb
  obtain ⟨y, hy⟩ := hlifts (e₀ b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  refine ⟨Algebra.TensorProduct.rTensor D₀ j y, ?_⟩
  rw [hmap, htransfer, hy, e₀.symm_apply_apply]

end SmoothData

end Algebra.Smooth.FiniteModel
namespace Algebra.Smooth.FiniteModel
universe u v
variable {C : Type u} [CommRing C] {B : Type v} [CommRing B] [Algebra C B]
/-- The total smooth model ring is finite type over the integers. -/
theorem model_finiteType (A : Subalgebra ℤ C) (D : Type u)
    [CommRing D] [Algebra A D] [Algebra.Smooth A D] (hA : A.FG) :
    Algebra.FiniteType ℤ D :=
  Algebra.FiniteType.trans (A.fg_iff_finiteType.mp hA) inferInstance

end Algebra.Smooth.FiniteModel
