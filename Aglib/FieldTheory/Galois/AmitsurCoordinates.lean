/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Galois.TensorProductCochains
public import Aglib.Algebra.Homology.Amitsur.Conerve
public import Mathlib.Tactic.FinCases

/-! # Galois coordinates on the original Amitsur terms

The source is the native wide-pushout conerve of the original algebra map.
Its canonical successor tensor isomorphisms identify degrees one through three
with the actual Galois tensor coordinates. These are algebra equivalences of
the original terms, not new cohomology carriers.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Algebra.Amitsur

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The actual degree-zero Amitsur term is the original extension algebra. -/
def zeroAlgEquiv : term K L 0 ≃ₐ[K] L := CommAlgCat.algEquivOfIso (zeroIso K L)

/-- The actual degree-one Amitsur term is the binary tensor product. -/
def oneTensorEquiv : term K L 1 ≃ₐ[K] L ⊗[K] L :=
  (CommAlgCat.algEquivOfIso (successorTensorIso K L 0)).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (zeroAlgEquiv K L))

/-- The actual degree-two Amitsur term is the right-associated triple tensor product. -/
def twoTensorEquiv : term K L 2 ≃ₐ[K] L ⊗[K] (L ⊗[K] L) :=
  (CommAlgCat.algEquivOfIso (successorTensorIso K L 1)).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (oneTensorEquiv K L))

/-- The actual degree-three Amitsur term is the right-associated fourfold tensor product. -/
def threeTensorEquiv : term K L 3 ≃ₐ[K] L ⊗[K] (L ⊗[K] (L ⊗[K] L)) :=
  (CommAlgCat.algEquivOfIso (successorTensorIso K L 2)).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (twoTensorEquiv K L))

/-- The zero-term identification keeps its original factor map. -/
@[simp]
theorem zeroAlgEquiv_ι (i : Fin 1) (x : L) :
    zeroAlgEquiv K L ((ι K L 0 i).hom x) = x :=
  congrArg (fun f : CommAlgCat.of K L ⟶ CommAlgCat.of K L => f.hom x) (ι_zeroTo K L i)

/-- Splitting off the first factor retains the original zeroth inclusion. -/
@[simp]
theorem successorTensorEquiv_ι_zero (n : ℕ) (x : L) :
    CommAlgCat.algEquivOfIso (successorTensorIso K L n)
      ((ι K L (n + 1) 0).hom x) = x ⊗ₜ[K] (1 : term K L n) :=
  congrArg (fun f : CommAlgCat.of K L ⟶ CommAlgCat.of K (L ⊗[K] term K L n) =>
    f.hom x) (ι_successorToTensor K L n 0)

/-- Splitting off the first factor retains every original remaining inclusion. -/
@[simp]
theorem successorTensorEquiv_ι_succ (n : ℕ) (i : Fin (n + 1)) (x : L) :
    CommAlgCat.algEquivOfIso (successorTensorIso K L n)
      ((ι K L (n + 1) i.succ).hom x) = (1 : L) ⊗ₜ[K] ((ι K L n i).hom x) :=
  congrArg (fun f : CommAlgCat.of K L ⟶ CommAlgCat.of K (L ⊗[K] term K L n) =>
    f.hom x) (ι_successorToTensor K L n i.succ)

variable [FiniteDimensional K L] [IsGalois K L]

/-- Original degree-one conerve coordinates indexed by the actual Galois group. -/
def oneGaloisEquiv : term K L 1 ≃ₐ[K] (Gal(L/K) → L) :=
  (oneTensorEquiv K L).trans ((IsGalois.tensorProductEquivPi K L).restrictScalars K)

/-- Original degree-two conerve coordinates, in argument order tau, sigma. -/
def twoGaloisEquiv : term K L 2 ≃ₐ[K] (Gal(L/K) → Gal(L/K) → L) :=
  (twoTensorEquiv K L).trans ((IsGalois.tripleTensorEquivPi K L).restrictScalars K)

/-- Original degree-three conerve coordinates, in argument order upsilon, tau, sigma. -/
def threeGaloisEquiv : term K L 3 ≃ₐ[K] (Gal(L/K) → Gal(L/K) → Gal(L/K) → L) :=
  (threeTensorEquiv K L).trans ((IsGalois.quadrupleTensorEquivPi K L).restrictScalars K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original degree-one factor has its literal Galois evaluation. -/
theorem oneGaloisEquiv_ι (i : Fin 2) (x : L) (σ : Gal(L/K)) :
    oneGaloisEquiv K L ((ι K L 1 i).hom x) σ = Fin.cases x (fun _ => σ x) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change IsGalois.tensorProductEquivPi K L
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (zeroAlgEquiv K L))
        (CommAlgCat.algEquivOfIso (successorTensorIso K L 0)
          ((ι K L 1 0).hom x))) σ = x
    rw [successorTensorEquiv_ι_zero K L 0 x]
    simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  · change IsGalois.tensorProductEquivPi K L
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (zeroAlgEquiv K L))
        (CommAlgCat.algEquivOfIso (successorTensorIso K L 0)
          ((ι K L 1 j.succ).hom x))) σ = σ x
    rw [successorTensorEquiv_ι_succ K L 0 j x]
    simp only [Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, AlgEquiv.coe_toAlgHom,
      IsGalois.tensorProductEquivPi_tmul, one_mul, EmbeddingLike.apply_eq_iff_eq]
    exact zeroAlgEquiv_ι K L j x

private theorem triple_left_one (z : L ⊗[K] L) (σ τ : Gal(L/K)) :
    IsGalois.tripleTensorEquivPi K L (1 ⊗ₜ[K] z) τ σ =
      σ (IsGalois.tensorProductEquivPi K L z τ) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add a b ha hb => simp [TensorProduct.tmul_add, ha, hb]

private theorem quadruple_left_one (z : L ⊗[K] (L ⊗[K] L))
    (σ τ υ : Gal(L/K)) :
    IsGalois.quadrupleTensorEquivPi K L (1 ⊗ₜ[K] z) υ τ σ =
      σ (IsGalois.tripleTensorEquivPi K L z υ τ) := by
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    induction z using TensorProduct.inductionOn with
    | tmul b c => simp [map_mul, mul_assoc]
    | add b c hb hc => simp [TensorProduct.tmul_add, hb, hc]
  | add a b ha hb => simp [TensorProduct.tmul_add, ha, hb]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original degree-two factor has its cumulative Galois evaluation. -/
theorem twoGaloisEquiv_ι (i : Fin 3) (x : L) (σ τ : Gal(L/K)) :
    twoGaloisEquiv K L ((ι K L 2 i).hom x) τ σ =
      Fin.cases x (Fin.cases (σ x) (fun _ => (σ * τ) x)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change IsGalois.tripleTensorEquivPi K L
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (oneTensorEquiv K L))
        (CommAlgCat.algEquivOfIso (successorTensorIso K L 1)
          ((ι K L 2 0).hom x))) τ σ = x
    rw [successorTensorEquiv_ι_zero K L 1 x]
    simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.one_def]
  · change IsGalois.tripleTensorEquivPi K L
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (oneTensorEquiv K L))
        (CommAlgCat.algEquivOfIso (successorTensorIso K L 1)
          ((ι K L 2 j.succ).hom x))) τ σ =
        Fin.cases (σ x) (fun _ => (σ * τ) x) j
    rw [successorTensorEquiv_ι_succ K L 1 j x]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    rw [triple_left_one K L]
    change σ (oneGaloisEquiv K L ((ι K L 1 j).hom x) τ) = _
    rw [oneGaloisEquiv_ι]
    refine Fin.cases ?_ (fun _ => ?_) j <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original degree-three factor has its cumulative Galois evaluation. -/
theorem threeGaloisEquiv_ι (i : Fin 4) (x : L) (σ τ υ : Gal(L/K)) :
    threeGaloisEquiv K L ((ι K L 3 i).hom x) υ τ σ =
      Fin.cases x (Fin.cases (σ x) (Fin.cases ((σ * τ) x)
        (fun _ => (σ * τ * υ) x))) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change IsGalois.quadrupleTensorEquivPi K L
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (twoTensorEquiv K L))
        (CommAlgCat.algEquivOfIso (successorTensorIso K L 2)
          ((ι K L 3 0).hom x))) υ τ σ = x
    rw [successorTensorEquiv_ι_zero K L 2 x]
    simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.one_def]
  · change IsGalois.quadrupleTensorEquivPi K L
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) (twoTensorEquiv K L))
        (CommAlgCat.algEquivOfIso (successorTensorIso K L 2)
          ((ι K L 3 j.succ).hom x))) υ τ σ =
        Fin.cases (σ x) (Fin.cases ((σ * τ) x) (fun _ => (σ * τ * υ) x)) j
    rw [successorTensorEquiv_ι_succ K L 2 j x]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    rw [quadruple_left_one K L]
    change σ (twoGaloisEquiv K L ((ι K L 2 j).hom x) υ τ) = _
    rw [twoGaloisEquiv_ι]
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun _ => ?_) k <;> rfl

end Algebra.Amitsur
