/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Descent.FinitePresentation.Models
public import Mathlib.Algebra.Module.Projective

/-!
# Actual maps between finite matrix cokernels

A linear map between actual finite matrix cokernels has a finite matrix lift
and a finite matrix witnessing preservation of the original relations. Over
an actual filtered ring colimit both matrices descend, and their relation
equation holds at one common later stage. The quotient-projection equation
retains the original linear map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Limits
open scoped Matrix

namespace ModuleCat

variable {R : Type u} [CommRing R] {a b c d : ℕ}

/-- A matrix carrying the original relation matrix into the target relation
matrix induces the native map of their actual quotient modules. -/
def matrixCokernelMap (A : Matrix (Fin b) (Fin a) R)
    (B : Matrix (Fin d) (Fin c) R) (D : Matrix (Fin d) (Fin b) R)
    (E : Matrix (Fin c) (Fin a) R) (h : D * A = B * E) :
    ((Fin b → R) ⧸ LinearMap.range A.mulVecLin) →ₗ[R]
      ((Fin d → R) ⧸ LinearMap.range B.mulVecLin) :=
  (LinearMap.range A.mulVecLin).mapQ (LinearMap.range B.mulVecLin) D.mulVecLin (by
    rintro _ ⟨x, rfl⟩
    refine ⟨E.mulVecLin x, ?_⟩
    have hlin : D.mulVecLin.comp A.mulVecLin = B.mulVecLin.comp E.mulVecLin := by
      rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, h]
    exact (DFunLike.congr_fun hlin x).symm)

/-- The induced map retains its original quotient projection. -/
theorem matrixCokernelMap_mkQ (A : Matrix (Fin b) (Fin a) R)
    (B : Matrix (Fin d) (Fin c) R) (D : Matrix (Fin d) (Fin b) R)
    (E : Matrix (Fin c) (Fin a) R) (h : D * A = B * E) (x : Fin b → R) :
    matrixCokernelMap A B D E h ((LinearMap.range A.mulVecLin).mkQ x) =
      (LinearMap.range B.mulVecLin).mkQ (D.mulVecLin x) := rfl

/-- Every actual linear map between finite matrix cokernels has a finite
matrix lift and a finite witness for the original relation equation. -/
theorem exists_matrixCokernelMap (A : Matrix (Fin b) (Fin a) R)
    (B : Matrix (Fin d) (Fin c) R)
    (f : ((Fin b → R) ⧸ LinearMap.range A.mulVecLin) →ₗ[R]
      ((Fin d → R) ⧸ LinearMap.range B.mulVecLin)) :
    ∃ (D : Matrix (Fin d) (Fin b) R) (E : Matrix (Fin c) (Fin a) R),
      D * A = B * E ∧
      ∀ x, f ((LinearMap.range A.mulVecLin).mkQ x) =
        (LinearMap.range B.mulVecLin).mkQ (D.mulVecLin x) := by
  classical
  obtain ⟨D, hD⟩ := Module.projective_lifting_property
    (LinearMap.range B.mulVecLin).mkQ
    (f.comp (LinearMap.range A.mulVecLin).mkQ)
    (LinearMap.range B.mulVecLin).mkQ_surjective
  have hDA (x : Fin a → R) : D (A.mulVecLin x) ∈ LinearMap.range B.mulVecLin := by
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range B.mulVecLin)).mp
    change (LinearMap.range B.mulVecLin).mkQ (D (A.mulVecLin x)) = 0
    have hDx := DFunLike.congr_fun hD (A.mulVecLin x)
    simp only [LinearMap.comp_apply] at hDx
    rw [hDx]
    have hx : (LinearMap.range A.mulVecLin).mkQ (A.mulVecLin x) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range A.mulVecLin)).mpr ⟨x, rfl⟩
    rw [hx, map_zero]
  let DA := (D.comp A.mulVecLin).codRestrict (LinearMap.range B.mulVecLin) hDA
  obtain ⟨E, hE⟩ := Module.projective_lifting_property B.mulVecLin.rangeRestrict DA
    B.mulVecLin.surjective_rangeRestrict
  have hcomp : D.comp A.mulVecLin = B.mulVecLin.comp E := by
    apply LinearMap.ext
    intro x
    exact (congrArg Subtype.val (DFunLike.congr_fun hE x)).symm
  refine ⟨LinearMap.toMatrix' D, LinearMap.toMatrix' E, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
      Matrix.toLin'_toMatrix']
    exact hcomp
  · intro x
    change f ((LinearMap.range A.mulVecLin).mkQ x) =
      (LinearMap.range B.mulVecLin).mkQ (Matrix.toLin' (LinearMap.toMatrix' D) x)
    rw [Matrix.toLin'_toMatrix']
    exact (DFunLike.congr_fun hD x).symm

/-- A finite relation witness makes the corresponding actual quotient maps
equal. This is the equation used for functor and inverse identities. -/
theorem matrixCokernelMap_eq_of_sub_eq_mul
    (A : Matrix (Fin b) (Fin a) R) (B : Matrix (Fin d) (Fin c) R)
    (D D' : Matrix (Fin d) (Fin b) R) (E E' : Matrix (Fin c) (Fin a) R)
    (h : D * A = B * E) (h' : D' * A = B * E')
    (H : Matrix (Fin c) (Fin b) R) (hH : D - D' = B * H) :
    matrixCokernelMap A B D E h = matrixCokernelMap A B D' E' h' := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range A.mulVecLin).mkQ_surjective z
  rw [matrixCokernelMap_mkQ, matrixCokernelMap_mkQ]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range B.mulVecLin)).mpr
  refine ⟨H.mulVecLin x, ?_⟩
  have hlin : D.mulVecLin - D'.mulVecLin = B.mulVecLin.comp H.mulVecLin := by
    apply LinearMap.ext
    intro y
    change D.mulVec y - D'.mulVec y = B.mulVec (H.mulVec y)
    rw [← Matrix.sub_mulVec, hH, Matrix.mulVec_mulVec]
  exact (DFunLike.congr_fun hlin x).symm

end ModuleCat

section FilteredEquations

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc in
private theorem exists_common_ringEqualities {T : Type v} [Finite T] {i : I}
    (x y : T → F.obj i) (h : ∀ t, c.ι.app i (x t) = c.ι.app i (y t)) :
    ∃ (j : I) (q : i ⟶ j), ∀ t, F.map q (x t) = F.map q (y t) := by
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  choose j q hq using fun t ↦
    (Types.FilteredColimit.isColimit_eq_iff' hc' (x t) (y t)).mp (h t)
  obtain ⟨k, q₀, g, hg⟩ := IsFiltered.wideSpan q
  refine ⟨k, q₀, fun t ↦ ?_⟩
  have heq := congrArg (F.map (g t)) (hq t)
  change (F.map (q t) ≫ F.map (g t)) (x t) =
    (F.map (q t) ≫ F.map (g t)) (y t) at heq
  simpa only [← F.map_comp, hg t] using heq

include hc in
/-- An actual linear map between the colimit scalar extensions of two fixed
finite matrix presentations descends above their original stage. The output
matrices induce the native `matrixCokernelMap`, and the final equation
identifies its mapped matrix with the original map on every quotient
generator. -/
theorem ModuleCat.exists_matrixCokernelMap_above_of_isColimit
    (i : I) {a b c' d : ℕ}
    (A : Matrix (Fin b) (Fin a) (F.obj i))
    (B : Matrix (Fin d) (Fin c') (F.obj i))
    (f : ((Fin b → c.pt) ⧸ LinearMap.range (A.map (c.ι.app i).hom).mulVecLin) →ₗ[c.pt]
      ((Fin d → c.pt) ⧸ LinearMap.range (B.map (c.ι.app i).hom).mulVecLin)) :
    ∃ (j : I) (q : i ⟶ j)
      (D : Matrix (Fin d) (Fin b) (F.obj j))
      (E : Matrix (Fin c') (Fin a) (F.obj j)),
      D * A.map (F.map q).hom = B.map (F.map q).hom * E ∧
      ∀ x, f ((LinearMap.range (A.map (c.ι.app i).hom).mulVecLin).mkQ x) =
        (LinearMap.range (B.map (c.ι.app i).hom).mulVecLin).mkQ
          ((D.map (c.ι.app j).hom).mulVecLin x) := by
  classical
  obtain ⟨D, E, hDE, hf⟩ := ModuleCat.exists_matrixCokernelMap
    (R := c.pt)
    (A.map (c.ι.app i).hom) (B.map (c.ι.app i).hom) f
  let coefficients : (Fin d × Fin b) ⊕ (Fin c' × Fin a) → c.pt :=
    Sum.elim (fun z ↦ D z.1 z.2) (fun z ↦ E z.1 z.2)
  obtain ⟨k, hk⟩ := CommRingCat.exists_finite_subset_range_ι_app F c hc
    (Set.range coefficients) (Set.finite_range _)
  choose v hv using fun z ↦ hk (Set.mem_range_self z)
  let j := IsFiltered.max i k
  let q : i ⟶ j := IsFiltered.leftToMax i k
  let r : k ⟶ j := IsFiltered.rightToMax i k
  let D₀ : Matrix (Fin d) (Fin b) (F.obj j) := fun x y ↦ F.map r (v (.inl (x, y)))
  let E₀ : Matrix (Fin c') (Fin a) (F.obj j) := fun x y ↦ F.map r (v (.inr (x, y)))
  have hD₀ : D₀.map (c.ι.app j).hom = D := by
    ext x y
    change (F.map r ≫ c.ι.app j) (v (.inl (x, y))) = D x y
    rw [c.w]
    exact hv (.inl (x, y))
  have hE₀ : E₀.map (c.ι.app j).hom = E := by
    ext x y
    change (F.map r ≫ c.ι.app j) (v (.inr (x, y))) = E x y
    rw [c.w]
    exact hv (.inr (x, y))
  have hA : (A.map (F.map q).hom).map (c.ι.app j).hom = A.map (c.ι.app i).hom := by
    ext x y
    change (F.map q ≫ c.ι.app j) (A x y) = c.ι.app i (A x y)
    rw [c.w]
    rfl
  have hB : (B.map (F.map q).hom).map (c.ι.app j).hom = B.map (c.ι.app i).hom := by
    ext x y
    change (F.map q ≫ c.ι.app j) (B x y) = c.ι.app i (B x y)
    rw [c.w]
    rfl
  have hrel : (D₀ * A.map (F.map q).hom).map (c.ι.app j).hom =
      (B.map (F.map q).hom * E₀).map (c.ι.app j).hom := by
    rw [Matrix.map_mul, Matrix.map_mul, hD₀, hE₀, hA, hB]
    exact hDE
  obtain ⟨l, s, hs⟩ := exists_common_ringEqualities F c hc
    (fun z : Fin d × Fin a ↦ (D₀ * A.map (F.map q).hom) z.1 z.2)
    (fun z : Fin d × Fin a ↦ (B.map (F.map q).hom * E₀) z.1 z.2)
    (fun z ↦ congrFun (congrFun hrel z.1) z.2)
  refine ⟨l, q ≫ s, D₀.map (F.map s).hom, E₀.map (F.map s).hom, ?_, ?_⟩
  · have heq : (D₀ * A.map (F.map q).hom).map (F.map s).hom =
        (B.map (F.map q).hom * E₀).map (F.map s).hom := by
      ext x y
      exact hs (x, y)
    rw [Matrix.map_mul, Matrix.map_mul] at heq
    convert heq using 1 <;> ext x y <;> simp [Functor.map_comp]
  · have hD : (D₀.map (F.map s).hom).map (c.ι.app l).hom = D := by
      ext x y
      change (F.map s ≫ c.ι.app l) (D₀ x y) = D x y
      rw [c.w]
      exact congrFun (congrFun hD₀ x) y
    intro x
    rw [hD]
    exact hf x

end FilteredEquations

namespace ModuleCat

variable {R : Type u} [CommRing R] {b c d : ℕ}

/-- Equality of the actual quotient projections has a finite relation
witness in the original target relation matrix. -/
theorem exists_matrix_relation_of_quotient_eq
    (B : Matrix (Fin d) (Fin c) R) (D D' : Matrix (Fin d) (Fin b) R)
    (h : ∀ x, (LinearMap.range B.mulVecLin).mkQ (D.mulVecLin x) =
      (LinearMap.range B.mulVecLin).mkQ (D'.mulVecLin x)) :
    ∃ H : Matrix (Fin c) (Fin b) R, D - D' = B * H := by
  classical
  have hmem (x : Fin b → R) : (D - D').mulVecLin x ∈ LinearMap.range B.mulVecLin := by
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range B.mulVecLin)).mp
    change (LinearMap.range B.mulVecLin).mkQ ((D - D').mulVec x) = 0
    rw [Matrix.sub_mulVec, map_sub, sub_eq_zero]
    exact h x
  let L := (D - D').mulVecLin.codRestrict (LinearMap.range B.mulVecLin) hmem
  obtain ⟨H, hH⟩ := Module.projective_lifting_property B.mulVecLin.rangeRestrict L
    B.mulVecLin.surjective_rangeRestrict
  refine ⟨LinearMap.toMatrix' H, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  exact (congrArg Subtype.val (DFunLike.congr_fun hH x)).symm

end ModuleCat

section FilteredEquations

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc in
/-- A specified finite matrix factorization over the colimit descends above
its original stage, retaining the original factor under the cocone map. -/
theorem ModuleCat.exists_matrix_factorization_above_of_isColimit
    (i : I) {b c' d : ℕ}
    (D : Matrix (Fin d) (Fin b) (F.obj i))
    (B : Matrix (Fin d) (Fin c') (F.obj i))
    (H : Matrix (Fin c') (Fin b) c.pt)
    (h : (D.map (c.ι.app i).hom : Matrix (Fin d) (Fin b) c.pt) =
      (B.map (c.ι.app i).hom : Matrix (Fin d) (Fin c') c.pt) * H) :
    ∃ (j : I) (q : i ⟶ j) (H' : Matrix (Fin c') (Fin b) (F.obj j)),
      D.map (F.map q).hom = B.map (F.map q).hom * H' ∧
      H'.map (c.ι.app j).hom = H := by
  classical
  obtain ⟨k, hk⟩ := CommRingCat.exists_finite_subset_range_ι_app F c hc
    (Set.range fun z : Fin c' × Fin b ↦ H z.1 z.2) (Set.finite_range _)
  choose v hv using fun z : Fin c' × Fin b ↦ hk (Set.mem_range_self z)
  let j := IsFiltered.max i k
  let q : i ⟶ j := IsFiltered.leftToMax i k
  let r : k ⟶ j := IsFiltered.rightToMax i k
  let H₀ : Matrix (Fin c') (Fin b) (F.obj j) := fun x y ↦ F.map r (v (x, y))
  have hH₀ : H₀.map (c.ι.app j).hom = H := by
    ext x y
    change (F.map r ≫ c.ι.app j) (v (x, y)) = H x y
    rw [c.w]
    exact hv (x, y)
  have hD : (D.map (F.map q).hom).map (c.ι.app j).hom = D.map (c.ι.app i).hom := by
    ext x y
    change (F.map q ≫ c.ι.app j) (D x y) = c.ι.app i (D x y)
    rw [c.w]
    rfl
  have hB : (B.map (F.map q).hom).map (c.ι.app j).hom = B.map (c.ι.app i).hom := by
    ext x y
    change (F.map q ≫ c.ι.app j) (B x y) = c.ι.app i (B x y)
    rw [c.w]
    rfl
  have hrel : (D.map (F.map q).hom).map (c.ι.app j).hom =
      (B.map (F.map q).hom * H₀).map (c.ι.app j).hom := by
    rw [Matrix.map_mul, hD, hB, hH₀]
    exact h
  obtain ⟨l, s, hs⟩ := exists_common_ringEqualities F c hc
    (fun z : Fin d × Fin b ↦ (D.map (F.map q).hom) z.1 z.2)
    (fun z : Fin d × Fin b ↦ (B.map (F.map q).hom * H₀) z.1 z.2)
    (fun z ↦ congrFun (congrFun hrel z.1) z.2)
  refine ⟨l, q ≫ s, H₀.map (F.map s).hom, ?_, ?_⟩
  · have heq : (D.map (F.map q).hom).map (F.map s).hom =
        (B.map (F.map q).hom * H₀).map (F.map s).hom := by
      ext x y
      exact hs (x, y)
    rw [Matrix.map_mul] at heq
    convert heq using 1 <;> ext x y <;> simp [Functor.map_comp]
  · ext x y
    change (F.map s ≫ c.ι.app l) (H₀ x y) = H x y
    rw [c.w]
    exact congrFun (congrFun hH₀ x) y

include hc in
/-- Equality of specified actual matrix-cokernel maps holds at a later stage,
with an explicit finite witness in the original relation image. -/
theorem ModuleCat.exists_matrixCokernel_equality_above_of_isColimit
    (i : I) {b c' d : ℕ}
    (B : Matrix (Fin d) (Fin c') (F.obj i))
    (D D' : Matrix (Fin d) (Fin b) (F.obj i))
    (h : ∀ x,
      (LinearMap.range (B.map (c.ι.app i).hom).mulVecLin).mkQ
          ((D.map (c.ι.app i).hom).mulVecLin x) =
        (LinearMap.range (B.map (c.ι.app i).hom).mulVecLin).mkQ
          ((D'.map (c.ι.app i).hom).mulVecLin x)) :
    ∃ (j : I) (q : i ⟶ j) (H : Matrix (Fin c') (Fin b) (F.obj j)),
      D.map (F.map q).hom - D'.map (F.map q).hom = B.map (F.map q).hom * H := by
  obtain ⟨H, hH⟩ := ModuleCat.exists_matrix_relation_of_quotient_eq
    (R := c.pt)
    (B.map (c.ι.app i).hom) (D.map (c.ι.app i).hom) (D'.map (c.ι.app i).hom) h
  obtain ⟨j, q, H', hq, _⟩ := ModuleCat.exists_matrix_factorization_above_of_isColimit
    F c hc i (D - D') B H (by
      calc
        ((D - D').map (c.ι.app i).hom : Matrix (Fin d) (Fin b) c.pt) =
            D.map (c.ι.app i).hom - D'.map (c.ι.app i).hom := by
          ext x y
          exact map_sub (c.ι.app i).hom (D x y) (D' x y)
        _ = _ := hH)
  refine ⟨j, q, H', ?_⟩
  calc
    D.map (F.map q).hom - D'.map (F.map q).hom = (D - D').map (F.map q).hom := by
      ext x y
      exact (map_sub (F.map q).hom (D x y) (D' x y)).symm
    _ = _ := hq

end FilteredEquations

namespace ModuleCat

variable {R : Type u} [CommRing R] {a b c d : ℕ}

/-- A finite inverse equation modulo the original relation image is the
actual inverse equation for the induced quotient maps. -/
theorem matrixCokernelMap_comp_eq_id
    (A : Matrix (Fin b) (Fin a) R) (B : Matrix (Fin d) (Fin c) R)
    (D : Matrix (Fin d) (Fin b) R) (E : Matrix (Fin c) (Fin a) R)
    (h : D * A = B * E)
    (D' : Matrix (Fin b) (Fin d) R) (E' : Matrix (Fin a) (Fin c) R)
    (h' : D' * B = A * E')
    (H : Matrix (Fin a) (Fin b) R) (hH : D' * D - 1 = A * H) :
    (matrixCokernelMap B A D' E' h').comp (matrixCokernelMap A B D E h) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range A.mulVecLin).mkQ_surjective z
  simp only [LinearMap.comp_apply, matrixCokernelMap_mkQ, LinearMap.id_apply]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range A.mulVecLin)).mpr
  refine ⟨H.mulVecLin x, ?_⟩
  have hx := congrArg (fun T : Matrix (Fin b) (Fin b) R ↦ T.mulVec x) hH
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at hx
  exact hx.symm

/-- Actual inverse equations modulo the original relation images give a
native equivalence of the original quotient modules. -/
def matrixCokernelEquiv
    (A : Matrix (Fin b) (Fin a) R) (B : Matrix (Fin d) (Fin c) R)
    (D : Matrix (Fin d) (Fin b) R) (E : Matrix (Fin c) (Fin a) R)
    (h : D * A = B * E)
    (D' : Matrix (Fin b) (Fin d) R) (E' : Matrix (Fin a) (Fin c) R)
    (h' : D' * B = A * E')
    (H : Matrix (Fin a) (Fin b) R) (hH : D' * D - 1 = A * H)
    (K : Matrix (Fin c) (Fin d) R) (hK : D * D' - 1 = B * K) :
    ((Fin b → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[R]
      ((Fin d → R) ⧸ LinearMap.range B.mulVecLin) :=
  LinearEquiv.ofLinearMap (matrixCokernelMap A B D E h) (matrixCokernelMap B A D' E' h')
    (matrixCokernelMap_comp_eq_id B A D' E' h' D E h K hK)
    (matrixCokernelMap_comp_eq_id A B D E h D' E' h' H hH)

end ModuleCat

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The native scalar-extension/cokernel comparison commutes with the
original finite free quotient projection. -/
theorem extendScalarsCokernelPiIso_mkQ (φ : R →+* S) {m n : ℕ}
    (g : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (extendScalars φ).map (ModuleCat.ofHom (LinearMap.range g).mkQ) ≫
        (extendScalarsCokernelPiIso φ g).hom =
      (extendScalarsPiIso φ n).hom ≫
        ModuleCat.ofHom
          (LinearMap.range ((LinearMap.toMatrix' g).map φ).mulVecLin).mkQ := by
  let E := extendScalars φ
  have : E.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).isLeftAdjoint
  have hq := range_mkQ_cokernelIsoRangeQuotient_inv (f := ModuleCat.ofHom g)
  change ModuleCat.ofHom (LinearMap.range g).mkQ ≫
      (cokernelIsoRangeQuotient (ModuleCat.ofHom g)).inv =
    cokernel.π (ModuleCat.ofHom g) at hq
  simp only [extendScalarsCokernelPiIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Functor.map_comp_assoc, hq, PreservesCokernel.π_iso_hom_assoc]
  simp only [cokernel.mapIso_hom, cokernel.map, cokernel.π_desc_assoc, Category.assoc,
    cokernel_π_cokernelIsoRangeQuotient_hom]
  rfl

open scoped ChangeOfRings TensorProduct

/-- On the original quotient generators, the native comparison applies the
specified ring homomorphism to the original finite vector. -/
theorem extendScalarsCokernelPiIso_one_tmul_mkQ (φ : R →+* S) {m n : ℕ}
    (g : (Fin m → R) →ₗ[R] (Fin n → R)) (x : Fin n → R) :
    (extendScalarsCokernelPiIso φ g).hom ((1 : S) ⊗ₜ[R,φ] ((LinearMap.range g).mkQ x)) =
      (LinearMap.range ((LinearMap.toMatrix' g).map φ).mulVecLin).mkQ (fun j ↦ φ (x j)) := by
  let : Algebra R S := φ.toAlgebra
  have h := ConcreteCategory.congr_hom (extendScalarsCokernelPiIso_mkQ φ g)
    ((1 : S) ⊗ₜ[R,φ] x)
  change (extendScalarsCokernelPiIso φ g).hom
      ((extendScalars φ).map (ModuleCat.ofHom (LinearMap.range g).mkQ) ((1 : S) ⊗ₜ[R,φ] x)) =
    (LinearMap.range ((LinearMap.toMatrix' g).map φ).mulVecLin).mkQ
      ((extendScalarsPiIso φ n).hom ((1 : S) ⊗ₜ[R,φ] x)) at h
  rw [ExtendScalars.map_tmul] at h
  convert h using 1
  congr 1
  funext j
  have hpoint := extendScalarsPiIso_tmul φ n (1 : S) x j
  simpa only [mul_one] using hpoint.symm

end ModuleCat

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] {a b c d : ℕ}

/-- The native quotient map induced by a specified commuting square of
finite free linear maps. -/
def cokernelMapOfCommute
    (g : (Fin a → R) →ₗ[R] (Fin b → R))
    (h : (Fin c → R) →ₗ[R] (Fin d → R))
    (D : (Fin b → R) →ₗ[R] (Fin d → R))
    (E : (Fin a → R) →ₗ[R] (Fin c → R))
    (w : D.comp g = h.comp E) :
    ((Fin b → R) ⧸ LinearMap.range g) →ₗ[R] ((Fin d → R) ⧸ LinearMap.range h) :=
  (LinearMap.range g).mapQ (LinearMap.range h) D (by
    rintro _ ⟨x, rfl⟩
    exact ⟨E x, (DFunLike.congr_fun w x).symm⟩)

/-- The induced quotient map retains the original free-module projection. -/
theorem cokernelMapOfCommute_mkQ
    (g : (Fin a → R) →ₗ[R] (Fin b → R))
    (h : (Fin c → R) →ₗ[R] (Fin d → R))
    (D : (Fin b → R) →ₗ[R] (Fin d → R))
    (E : (Fin a → R) →ₗ[R] (Fin c → R))
    (w : D.comp g = h.comp E) (x : Fin b → R) :
    cokernelMapOfCommute g h D E w ((LinearMap.range g).mkQ x) =
      (LinearMap.range h).mkQ (D x) := rfl

/-- The specified commuting square remains the original coefficientwise
mapped square under the specified ring homomorphism. -/
theorem toMatrix_map_commutes
    (φ : R →+* S)
    (g : (Fin a → R) →ₗ[R] (Fin b → R))
    (h : (Fin c → R) →ₗ[R] (Fin d → R))
    (D : (Fin b → R) →ₗ[R] (Fin d → R))
    (E : (Fin a → R) →ₗ[R] (Fin c → R))
    (w : D.comp g = h.comp E) :
    (LinearMap.toMatrix' D).map φ * (LinearMap.toMatrix' g).map φ =
      (LinearMap.toMatrix' h).map φ * (LinearMap.toMatrix' E).map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul,
    ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, w]

open scoped ChangeOfRings TensorProduct

/-- The native scalar-extension/cokernel comparisons retain the original
quotient map, with its actual coefficientwise mapped matrix. -/
theorem extendScalarsCokernelPiIso_map
    (φ : R →+* S)
    (g : (Fin a → R) →ₗ[R] (Fin b → R))
    (h : (Fin c → R) →ₗ[R] (Fin d → R))
    (D : (Fin b → R) →ₗ[R] (Fin d → R))
    (E : (Fin a → R) →ₗ[R] (Fin c → R))
    (w : D.comp g = h.comp E) :
    (extendScalars φ).map (ModuleCat.ofHom (cokernelMapOfCommute g h D E w)) ≫
        (extendScalarsCokernelPiIso φ h).hom =
      (extendScalarsCokernelPiIso φ g).hom ≫
        ModuleCat.ofHom (matrixCokernelMap
          ((LinearMap.toMatrix' g).map φ) ((LinearMap.toMatrix' h).map φ)
          ((LinearMap.toMatrix' D).map φ) ((LinearMap.toMatrix' E).map φ)
          (toMatrix_map_commutes φ g h D E w)) := by
  let : Algebra R S := φ.toAlgebra
  apply ExtendScalars.hom_ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range g).mkQ_surjective z
  change (extendScalarsCokernelPiIso φ h).hom
      ((extendScalars φ).map (ModuleCat.ofHom (cokernelMapOfCommute g h D E w))
        ((1 : S) ⊗ₜ[R,φ] ((LinearMap.range g).mkQ x))) = _
  rw [ExtendScalars.map_tmul]
  change (extendScalarsCokernelPiIso φ h).hom
    ((1 : S) ⊗ₜ[R,φ] (cokernelMapOfCommute g h D E w ((LinearMap.range g).mkQ x))) = _
  rw [cokernelMapOfCommute_mkQ, extendScalarsCokernelPiIso_one_tmul_mkQ]
  change _ = matrixCokernelMap
    ((LinearMap.toMatrix' g).map φ) ((LinearMap.toMatrix' h).map φ)
    ((LinearMap.toMatrix' D).map φ) ((LinearMap.toMatrix' E).map φ)
    (toMatrix_map_commutes φ g h D E w)
    ((extendScalarsCokernelPiIso φ g).hom ((1 : S) ⊗ₜ[R,φ] ((LinearMap.range g).mkQ x)))
  rw [extendScalarsCokernelPiIso_one_tmul_mkQ, matrixCokernelMap_mkQ]
  congr 1
  funext j
  simpa only [Function.comp_def, LinearMap.toMatrix'_mulVec, Matrix.mulVecLin_apply] using
    RingHom.map_mulVec φ (LinearMap.toMatrix' D) x j

end ModuleCat

namespace ModuleCat

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

private theorem toMatrix_mulVecLin {m n : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    LinearMap.toMatrix' A.mulVecLin = A := by
  change LinearMap.toMatrix' (Matrix.toLin' A) = A
  exact LinearMap.toMatrix'_toLin' A

/-- The relation images in the two native descriptions of matrix scalar
extension are the same actual submodule. -/
theorem matrixCokernelBaseChange_range_eq
    (φ : R →+* S) {m n : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    LinearMap.range ((LinearMap.toMatrix' A.mulVecLin).map φ).mulVecLin =
      LinearMap.range (A.map φ).mulVecLin := by
  rw [toMatrix_mulVecLin]

/-- The actual scalar extension of a matrix cokernel is the actual cokernel
of its coefficientwise mapped matrix. -/
def matrixCokernelBaseChangeIso (φ : R →+* S) {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) R) :
    (extendScalars φ).obj (ModuleCat.of R ((Fin n → R) ⧸ LinearMap.range A.mulVecLin)) ≅
      ModuleCat.of S ((Fin n → S) ⧸ LinearMap.range (A.map φ).mulVecLin) :=
  extendScalarsCokernelPiIso φ A.mulVecLin ≪≫
    (Submodule.quotEquivOfEq _ _ (matrixCokernelBaseChange_range_eq φ A)).toModuleIso

open scoped ChangeOfRings TensorProduct

/-- The comparison retains the original quotient generators and scalar map. -/
theorem matrixCokernelBaseChangeIso_one_tmul_mkQ (φ : R →+* S) {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (x : Fin n → R) :
    (matrixCokernelBaseChangeIso φ A).hom
        ((1 : S) ⊗ₜ[R,φ] ((LinearMap.range A.mulVecLin).mkQ x)) =
      (LinearMap.range (A.map φ).mulVecLin).mkQ (fun j ↦ φ (x j)) := by
  let : Algebra R S := φ.toAlgebra
  change (Submodule.quotEquivOfEq _ _ (matrixCokernelBaseChange_range_eq φ A))
    ((extendScalarsCokernelPiIso φ A.mulVecLin).hom
      ((1 : S) ⊗ₜ[R,φ] ((LinearMap.range A.mulVecLin).mkQ x))) = _
  rw [extendScalarsCokernelPiIso_one_tmul_mkQ]
  rfl

/-- The actual scalar-extension map is the original mapped matrix-cokernel
map under the native comparisons. -/
theorem matrixCokernelBaseChangeIso_map
    (φ : R →+* S) {a b c d : ℕ}
    (A : Matrix (Fin b) (Fin a) R) (B : Matrix (Fin d) (Fin c) R)
    (D : Matrix (Fin d) (Fin b) R) (E : Matrix (Fin c) (Fin a) R)
    (h : D * A = B * E) :
    (extendScalars φ).map (ModuleCat.ofHom (matrixCokernelMap A B D E h)) ≫
        (matrixCokernelBaseChangeIso φ B).hom =
      (matrixCokernelBaseChangeIso φ A).hom ≫
        ModuleCat.ofHom (matrixCokernelMap (A.map φ) (B.map φ) (D.map φ) (E.map φ)
          (by rw [← Matrix.map_mul, ← Matrix.map_mul, h])) := by
  let : Algebra R S := φ.toAlgebra
  apply ExtendScalars.hom_ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range A.mulVecLin).mkQ_surjective z
  change (matrixCokernelBaseChangeIso φ B).hom
    ((extendScalars φ).map (ModuleCat.ofHom (matrixCokernelMap A B D E h))
      ((1 : S) ⊗ₜ[R,φ] ((LinearMap.range A.mulVecLin).mkQ x))) = _
  rw [ExtendScalars.map_tmul]
  change (matrixCokernelBaseChangeIso φ B).hom
    ((1 : S) ⊗ₜ[R,φ] (matrixCokernelMap A B D E h ((LinearMap.range A.mulVecLin).mkQ x))) = _
  rw [matrixCokernelMap_mkQ, matrixCokernelBaseChangeIso_one_tmul_mkQ]
  change _ = matrixCokernelMap (A.map φ) (B.map φ) (D.map φ) (E.map φ)
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, h])
    ((matrixCokernelBaseChangeIso φ A).hom
      ((1 : S) ⊗ₜ[R,φ] ((LinearMap.range A.mulVecLin).mkQ x)))
  rw [matrixCokernelBaseChangeIso_one_tmul_mkQ, matrixCokernelMap_mkQ]
  congr 1
  funext j
  simpa only [Matrix.mulVecLin_apply, Function.comp_def] using RingHom.map_mulVec φ D x j

/-- Original matrices retain their coefficient maps in a specified actual
commuting scalar triangle. -/
theorem matrix_map_comp_eq (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) {m n : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    A.map ρ = (A.map φ).map ψ := by
  ext x y
  exact (DFunLike.congr_fun hρ (A x y)).symm

/-- The actual cokernel comparisons for a specified commuting scalar
triangle, with its original ring maps. -/
def matrixCokernelCoconeIso (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) {m n : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    (extendScalars ρ).obj (ModuleCat.of R ((Fin n → R) ⧸ LinearMap.range A.mulVecLin)) ≅
      (extendScalars ψ).obj
        (ModuleCat.of S ((Fin n → S) ⧸ LinearMap.range (A.map φ).mulVecLin)) :=
  matrixCokernelBaseChangeIso ρ A ≪≫
    (Submodule.quotEquivOfEq _ _ (congrArg
      (fun M : Matrix (Fin n) (Fin m) T ↦ LinearMap.range M.mulVecLin)
      (matrix_map_comp_eq φ ψ ρ hρ A))).toModuleIso ≪≫
    (matrixCokernelBaseChangeIso ψ (A.map φ)).symm

/-- The scalar-triangle comparison retains the original stage quotient
generator under its actual first scalar map. -/
theorem matrixCokernelCoconeIso_one_tmul_mkQ
    (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) {m n : ℕ} (A : Matrix (Fin n) (Fin m) R) (x : Fin n → R) :
    (matrixCokernelCoconeIso φ ψ ρ hρ A).hom
        ((1 : T) ⊗ₜ[R,ρ] ((LinearMap.range A.mulVecLin).mkQ x)) =
      (1 : T) ⊗ₜ[S,ψ] ((LinearMap.range (A.map φ).mulVecLin).mkQ (fun j ↦ φ (x j))) := by
  let : Algebra R T := ρ.toAlgebra
  let : Algebra S T := ψ.toAlgebra
  let e := matrixCokernelBaseChangeIso ψ (A.map φ)
  apply e.toLinearEquiv.injective
  change e.hom ((matrixCokernelCoconeIso φ ψ ρ hρ A).hom
      ((1 : T) ⊗ₜ[R,ρ] ((LinearMap.range A.mulVecLin).mkQ x))) =
    e.hom ((1 : T) ⊗ₜ[S,ψ]
      ((LinearMap.range (A.map φ).mulVecLin).mkQ (fun j ↦ φ (x j))))
  rw [show e = matrixCokernelBaseChangeIso ψ (A.map φ) from rfl]
  rw [matrixCokernelBaseChangeIso_one_tmul_mkQ]
  change e.hom (e.inv ((Submodule.quotEquivOfEq _ _
      (congrArg (fun M : Matrix (Fin n) (Fin m) T ↦ LinearMap.range M.mulVecLin)
        (matrix_map_comp_eq φ ψ ρ hρ A)))
      ((matrixCokernelBaseChangeIso ρ A).hom
        ((1 : T) ⊗ₜ[R,ρ] ((LinearMap.range A.mulVecLin).mkQ x))))) = _
  rw [show ∀ y, e.hom (e.inv y) = y from e.toLinearEquiv.apply_symm_apply]
  rw [matrixCokernelBaseChangeIso_one_tmul_mkQ]
  change (LinearMap.range ((A.map φ).map ψ).mulVecLin).mkQ (fun j ↦ ρ (x j)) = _
  congr 1
  funext j
  exact (DFunLike.congr_fun hρ (x j)).symm

/-- Native scalar-extension composition for a specified actual scalar
triangle, using equality only to identify its composite ring map. -/
def extendScalarsCompOfEq (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) : extendScalars ρ ≅ extendScalars φ ⋙ extendScalars ψ :=
  eqToIso (congrArg (fun q : R →+* T ↦ extendScalars q) hρ.symm) ≪≫
    extendScalarsComp φ ψ

/-- The original unit tensor is retained by the actual scalar triangle. -/
theorem extendScalarsCompOfEq_hom_app_one_tmul
    (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) (M : ModuleCat.{u} R) (x : M) :
    (extendScalarsCompOfEq φ ψ ρ hρ).hom.app M ((1 : T) ⊗ₜ[R,ρ] x) =
      (1 : T) ⊗ₜ[S,ψ] ((1 : S) ⊗ₜ[R,φ] x) := by
  subst ρ
  exact extendScalarsComp_hom_app_one_tmul φ ψ M x

/-- The matrix-cokernel comparison is the native scalar-extension
composition comparison followed by the original stage cokernel comparison. -/
theorem matrixCokernelCoconeIso_eq_comp
    (φ : R →+* S) (ψ : S →+* T) (ρ : R →+* T)
    (hρ : ψ.comp φ = ρ) {m n : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    (matrixCokernelCoconeIso φ ψ ρ hρ A).hom =
      (extendScalarsCompOfEq φ ψ ρ hρ).hom.app
          (ModuleCat.of R ((Fin n → R) ⧸ LinearMap.range A.mulVecLin)) ≫
        (extendScalars ψ).map (matrixCokernelBaseChangeIso φ A).hom := by
  let : Algebra R T := ρ.toAlgebra
  let : Algebra S T := ψ.toAlgebra
  apply ExtendScalars.hom_ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range A.mulVecLin).mkQ_surjective z
  change _ = (extendScalars ψ).map (matrixCokernelBaseChangeIso φ A).hom
    ((extendScalarsCompOfEq φ ψ ρ hρ).hom.app _
      ((1 : T) ⊗ₜ[R,ρ] ((LinearMap.range A.mulVecLin).mkQ x)))
  rw [extendScalarsCompOfEq_hom_app_one_tmul, ExtendScalars.map_tmul]
  change _ = (1 : T) ⊗ₜ[S,ψ] ((matrixCokernelBaseChangeIso φ A).hom
    ((1 : S) ⊗ₜ[R,φ] ((LinearMap.range A.mulVecLin).mkQ x)))
  rw [matrixCokernelBaseChangeIso_one_tmul_mkQ, matrixCokernelCoconeIso_one_tmul_mkQ]

end ModuleCat

namespace ModuleCat

variable {I : Type u} [Category.{u} I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F)

/-- Native scalar-extension composition for the original filtered ring
cocone maps and one actual transition map. -/
def extendScalarsCoconeCompIso {i j : I} (q : i ⟶ j) :
    (extendScalars (c.ι.app i).hom : ModuleCat.{u} (F.obj i) ⥤ ModuleCat.{u} c.pt) ≅
      (extendScalars (F.map q).hom : ModuleCat.{u} (F.obj i) ⥤ ModuleCat.{u} (F.obj j)) ⋙
        (extendScalars (c.ι.app j).hom : ModuleCat.{u} (F.obj j) ⥤ ModuleCat.{u} c.pt) :=
  extendScalarsCompOfEq (F.map q).hom (c.ι.app j).hom (c.ι.app i).hom (by
    ext x
    change (F.map q ≫ c.ι.app j) x = c.ι.app i x
    rw [c.w]
    rfl)

variable [IsFiltered I] (hc : IsColimit c)

include hc in
/-- An actual map between scalar extensions of two given finite matrix
presentations descends to an actual map between their stage scalar
extensions. Its comparison square is the native cocone composition square. -/
theorem exists_matrix_hom_above_of_isColimit (i : I) {a b c' d : ℕ}
    (A : Matrix (Fin b) (Fin a) (F.obj i))
    (B : Matrix (Fin d) (Fin c') (F.obj i))
    (f : (extendScalars (c.ι.app i).hom).obj
        (ModuleCat.of (F.obj i) ((Fin b → F.obj i) ⧸ LinearMap.range A.mulVecLin)) ⟶
      (extendScalars (c.ι.app i).hom).obj
        (ModuleCat.of (F.obj i) ((Fin d → F.obj i) ⧸ LinearMap.range B.mulVecLin))) :
    ∃ (j : I) (q : i ⟶ j)
      (g : (extendScalars (F.map q).hom).obj
          (ModuleCat.of (F.obj i) ((Fin b → F.obj i) ⧸ LinearMap.range A.mulVecLin)) ⟶
        (extendScalars (F.map q).hom).obj
          (ModuleCat.of (F.obj i) ((Fin d → F.obj i) ⧸ LinearMap.range B.mulVecLin))),
      (extendScalarsCoconeCompIso F c q).hom.app
          (ModuleCat.of (F.obj i) ((Fin b → F.obj i) ⧸ LinearMap.range A.mulVecLin)) ≫
          (extendScalars (c.ι.app j).hom).map g =
        f ≫ (extendScalarsCoconeCompIso F c q).hom.app
          (ModuleCat.of (F.obj i) ((Fin d → F.obj i) ⧸ LinearMap.range B.mulVecLin)) := by
  classical
  let ρ : F.obj i →+* c.pt := (c.ι.app i).hom
  let M := ModuleCat.of (F.obj i) ((Fin b → F.obj i) ⧸ LinearMap.range A.mulVecLin)
  let N := ModuleCat.of (F.obj i) ((Fin d → F.obj i) ⧸ LinearMap.range B.mulVecLin)
  let eA := matrixCokernelBaseChangeIso ρ A
  let eB := matrixCokernelBaseChangeIso ρ B
  let f₀ : ModuleCat.of c.pt ((Fin b → c.pt) ⧸ LinearMap.range (A.map ρ).mulVecLin) ⟶
      ModuleCat.of c.pt ((Fin d → c.pt) ⧸ LinearMap.range (B.map ρ).mulVecLin) :=
    eA.inv ≫ f ≫ eB.hom
  obtain ⟨j, q, D, E, hDE, hf⟩ := exists_matrixCokernelMap_above_of_isColimit F c hc i A B f₀.hom
  let φ : F.obj i →+* F.obj j := (F.map q).hom
  let ψ : F.obj j →+* c.pt := (c.ι.app j).hom
  have hρ : ψ.comp φ = ρ := by
    ext x
    change (F.map q ≫ c.ι.app j) x = c.ι.app i x
    rw [c.w]
    rfl
  let Aⱼ := A.map φ
  let Bⱼ := B.map φ
  let G := ModuleCat.ofHom (matrixCokernelMap Aⱼ Bⱼ D E hDE)
  let eAφ := matrixCokernelBaseChangeIso φ A
  let eBφ := matrixCokernelBaseChangeIso φ B
  let eAⱼ := matrixCokernelBaseChangeIso ψ Aⱼ
  let eBⱼ := matrixCokernelBaseChangeIso ψ Bⱼ
  let α := matrixCokernelCoconeIso φ ψ ρ hρ A
  let β := matrixCokernelCoconeIso φ ψ ρ hρ B
  let Q₁ := (Submodule.quotEquivOfEq _ _ (congrArg
    (fun L : Matrix (Fin b) (Fin a) c.pt ↦ LinearMap.range L.mulVecLin)
    (matrix_map_comp_eq φ ψ ρ hρ A))).toModuleIso
  let Q₂ := (Submodule.quotEquivOfEq _ _ (congrArg
    (fun L : Matrix (Fin d) (Fin c') c.pt ↦ LinearMap.range L.mulVecLin)
    (matrix_map_comp_eq φ ψ ρ hρ B))).toModuleIso
  have hmap : (D.map ψ) * (Aⱼ.map ψ) = (Bⱼ.map ψ) * (E.map ψ) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hDE]
  let G₀ := ModuleCat.ofHom (matrixCokernelMap (Aⱼ.map ψ) (Bⱼ.map ψ)
    (D.map ψ) (E.map ψ) hmap)
  have hG₀ : Q₁.hom ≫ G₀ = f₀ ≫ Q₂.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := (LinearMap.range (A.map ρ).mulVecLin).mkQ_surjective z
    change matrixCokernelMap (Aⱼ.map ψ) (Bⱼ.map ψ) (D.map ψ) (E.map ψ) hmap
        ((LinearMap.range (Aⱼ.map ψ).mulVecLin).mkQ x) =
      Q₂.hom (f₀ ((LinearMap.range (A.map ρ).mulVecLin).mkQ x))
    rw [matrixCokernelMap_mkQ]
    have hfx : f₀.hom ((LinearMap.range (A.map ρ).mulVecLin).mkQ x) =
        (LinearMap.range (B.map ρ).mulVecLin).mkQ ((D.map ψ).mulVecLin x) := hf x
    change _ = Q₂.hom (f₀.hom ((LinearMap.range (A.map ρ).mulVecLin).mkQ x))
    rw [hfx]
    rfl
  have hα : α.hom ≫ eAⱼ.hom = eA.hom ≫ Q₁.hom := by
    simp only [α, matrixCokernelCoconeIso, eAⱼ, Aⱼ, eA, Q₁, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hβ : β.hom ≫ eBⱼ.hom = eB.hom ≫ Q₂.hom := by
    simp only [β, matrixCokernelCoconeIso, eBⱼ, Bⱼ, eB, Q₂, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hG : α.hom ≫ (extendScalars ψ).map G = f ≫ β.hom := by
    apply (cancel_mono eBⱼ.hom).mp
    calc
      (α.hom ≫ (extendScalars ψ).map G) ≫ eBⱼ.hom =
          (eA.hom ≫ Q₁.hom) ≫ G₀ := by
        rw [Category.assoc, matrixCokernelBaseChangeIso_map,
          ← Category.assoc, hα]
      _ = eA.hom ≫ (f₀ ≫ Q₂.hom) := by rw [Category.assoc, hG₀]
      _ = (f ≫ eB.hom) ≫ Q₂.hom := by
        simp only [f₀, Category.assoc, Iso.hom_inv_id_assoc]
      _ = (f ≫ β.hom) ≫ eBⱼ.hom := by simp only [Category.assoc, hβ]
  let g : (extendScalars φ).obj M ⟶ (extendScalars φ).obj N := eAφ.hom ≫ G ≫ eBφ.inv
  refine ⟨j, q, g, ?_⟩
  change (extendScalarsCompOfEq φ ψ ρ hρ).hom.app M ≫ (extendScalars ψ).map g =
    f ≫ (extendScalarsCompOfEq φ ψ ρ hρ).hom.app N
  calc
    _ = (α.hom ≫ (extendScalars ψ).map G) ≫ (extendScalars ψ).map eBφ.inv := by
      dsimp only [g]
      rw [Functor.map_comp, Functor.map_comp,
        ← Category.assoc, ← matrixCokernelCoconeIso_eq_comp]
      simp only [Category.assoc]
      rfl
    _ = (f ≫ β.hom) ≫ (extendScalars ψ).map eBφ.inv := by rw [hG]
    _ = _ := by
      rw [matrixCokernelCoconeIso_eq_comp, Category.assoc, Category.assoc,
        ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
      rfl

end ModuleCat

namespace CategoryTheory.NatIso

/-- Transport an actual stage map along original object isomorphisms and a
specified natural comparison with a composite scalar functor. -/
theorem hom_lift_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F₀ : A ⥤ C) (Fⱼ : A ⥤ B) (G : B ⥤ C) (u : F₀ ≅ Fⱼ ⋙ G)
    {P Q M N : A} (eM : P ≅ M) (eN : Q ≅ N) (f : F₀.obj M ⟶ F₀.obj N)
    (g : Fⱼ.obj P ⟶ Fⱼ.obj Q)
    (h : u.hom.app P ≫ G.map g =
      (F₀.map eM.hom ≫ f ≫ F₀.map eN.inv) ≫ u.hom.app Q) :
    u.hom.app M ≫ G.map (Fⱼ.map eM.inv ≫ g ≫ Fⱼ.map eN.hom) = f ≫ u.hom.app N := by
  have hM := (u.hom.naturality eM.inv).symm
  change u.hom.app M ≫ G.map (Fⱼ.map eM.inv) = F₀.map eM.inv ≫ u.hom.app P at hM
  have hN := (u.hom.naturality eN.hom).symm
  change u.hom.app Q ≫ G.map (Fⱼ.map eN.hom) = F₀.map eN.hom ≫ u.hom.app N at hN
  rw [Functor.map_comp, Functor.map_comp]
  calc
    _ = F₀.map eM.inv ≫ (u.hom.app P ≫ G.map g) ≫ G.map (Fⱼ.map eN.hom) := by
      rw [← Category.assoc, hM]
      simp only [Category.assoc]
    _ = F₀.map eM.inv ≫ (F₀.map eM.hom ≫ f ≫ F₀.map eN.inv) ≫
        u.hom.app Q ≫ G.map (Fⱼ.map eN.hom) := by rw [h]; simp only [Category.assoc]
    _ = _ := by
      simp only [Category.assoc]
      rw [hN]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]

end CategoryTheory.NatIso

namespace ModuleCat

private theorem exists_matrix_presentation_iso (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    ∃ (m n : ℕ) (A : Matrix (Fin n) (Fin m) R),
      Nonempty (ModuleCat.of R ((Fin n → R) ⧸ LinearMap.range A.mulVecLin) ≅ M) := by
  obtain ⟨n, m, p, g, hp, hgp⟩ := Module.FinitePresentation.exists_fin' R M
  let A := LinearMap.toMatrix' g
  have hg : A.mulVecLin = g := by
    apply LinearMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec g x
  refine ⟨m, n, A, ?_⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range hg)).toModuleIso ≪≫
    (hgp.linearEquivOfSurjective hp).toModuleIso⟩

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc in
/-- An actual linear map between the actual colimit scalar extensions of
two given fp modules descends above their original stage. The recovery
equation uses the original native cocone composition comparison. -/
theorem exists_hom_above_of_isColimit (i : I)
    (M N : ModuleCat.{u} (F.obj i))
    [Module.FinitePresentation (F.obj i) M] [Module.FinitePresentation (F.obj i) N]
    (f : (extendScalars (c.ι.app i).hom).obj M ⟶
      (extendScalars (c.ι.app i).hom).obj N) :
    ∃ (j : I) (q : i ⟶ j)
      (g : (extendScalars (F.map q).hom).obj M ⟶ (extendScalars (F.map q).hom).obj N),
      (extendScalarsCoconeCompIso F c q).hom.app M ≫ (extendScalars (c.ι.app j).hom).map g =
        f ≫ (extendScalarsCoconeCompIso F c q).hom.app N := by
  obtain ⟨a, b, A, ⟨eM⟩⟩ := exists_matrix_presentation_iso (F.obj i) M
  obtain ⟨c', d, B, ⟨eN⟩⟩ := exists_matrix_presentation_iso (F.obj i) N
  let F₀ := extendScalars (c.ι.app i).hom
  let f₀ := F₀.map eM.hom ≫ f ≫ F₀.map eN.inv
  obtain ⟨j, q, g, hg⟩ := exists_matrix_hom_above_of_isColimit F c hc i A B f₀
  let Fⱼ := extendScalars (F.map q).hom
  let G := extendScalars (c.ι.app j).hom
  refine ⟨j, q, Fⱼ.map eM.inv ≫ g ≫ Fⱼ.map eN.hom, ?_⟩
  exact CategoryTheory.NatIso.hom_lift_transport F₀ Fⱼ G
    (extendScalarsCoconeCompIso F c q) eM eN f g hg

include hc in
/-- Equality of two given fp-module maps after colimit scalar extension
holds after one actual later scalar extension. -/
theorem exists_hom_equality_above_of_isColimit (i : I)
    (M N : ModuleCat.{u} (F.obj i))
    [Module.FinitePresentation (F.obj i) M] [Module.FinitePresentation (F.obj i) N]
    (f g : M ⟶ N)
    (h : (extendScalars (c.ι.app i).hom).map f =
      (extendScalars (c.ι.app i).hom).map g) :
    ∃ (j : I) (q : i ⟶ j),
      (extendScalars (F.map q).hom).map f = (extendScalars (F.map q).hom).map g := by
  obtain ⟨a, b, A, ⟨eM⟩⟩ := exists_matrix_presentation_iso (F.obj i) M
  obtain ⟨c', d, B, ⟨eN⟩⟩ := exists_matrix_presentation_iso (F.obj i) N
  let f₀ := eM.hom ≫ f ≫ eN.inv
  let g₀ := eM.hom ≫ g ≫ eN.inv
  obtain ⟨D, E, hDE, hf⟩ := exists_matrixCokernelMap A B f₀.hom
  obtain ⟨D', E', hDE', hg⟩ := exists_matrixCokernelMap A B g₀.hom
  have hf₀ : ModuleCat.ofHom (matrixCokernelMap A B D E hDE) = f₀ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := (LinearMap.range A.mulVecLin).mkQ_surjective z
    exact (hf x).symm
  have hg₀ : ModuleCat.ofHom (matrixCokernelMap A B D' E' hDE') = g₀ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := (LinearMap.range A.mulVecLin).mkQ_surjective z
    exact (hg x).symm
  let ρ : F.obj i →+* c.pt := (c.ι.app i).hom
  have hfg₀ : (extendScalars ρ).map f₀ = (extendScalars ρ).map g₀ := by
    have hρmaps : (extendScalars ρ).map f = (extendScalars ρ).map g := h
    simp only [f₀, g₀, Functor.map_comp, hρmaps]
  have hlim : ∀ x,
      (LinearMap.range (B.map ρ).mulVecLin).mkQ ((D.map ρ).mulVecLin x) =
        (LinearMap.range (B.map ρ).mulVecLin).mkQ ((D'.map ρ).mulVecLin x) := by
    have hh := congrArg (fun k ↦ k ≫ (matrixCokernelBaseChangeIso ρ B).hom) hfg₀
    rw [← hf₀, ← hg₀, matrixCokernelBaseChangeIso_map,
      matrixCokernelBaseChangeIso_map] at hh
    have hh' := (cancel_epi (matrixCokernelBaseChangeIso ρ A).hom).mp hh
    intro x
    exact ConcreteCategory.congr_hom hh'
      ((LinearMap.range (A.map ρ).mulVecLin).mkQ x)
  obtain ⟨j, q, H, hH⟩ := exists_matrixCokernel_equality_above_of_isColimit F c hc i B D D' hlim
  let φ : F.obj i →+* F.obj j := (F.map q).hom
  have hmap : D.map φ * A.map φ = B.map φ * E.map φ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hDE]
  have hmap' : D'.map φ * A.map φ = B.map φ * E'.map φ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hDE']
  have heq := matrixCokernelMap_eq_of_sub_eq_mul (A.map φ) (B.map φ)
    (D.map φ) (D'.map φ) (E.map φ) (E'.map φ) hmap hmap' H hH
  have hstage : (extendScalars φ).map f₀ = (extendScalars φ).map g₀ := by
    apply (cancel_mono (matrixCokernelBaseChangeIso φ B).hom).mp
    rw [← hf₀, ← hg₀, matrixCokernelBaseChangeIso_map,
      matrixCokernelBaseChangeIso_map, heq]
  refine ⟨j, q, ?_⟩
  apply (cancel_epi ((extendScalars φ).map eM.hom)).mp
  apply (cancel_mono ((extendScalars φ).map eN.inv)).mp
  simpa only [f₀, g₀, Functor.map_comp, Category.assoc] using hstage

end ModuleCat
