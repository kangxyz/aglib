/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.DoubleLine.Marked

/-!
# Actual marked-chart coordinates and exceptional points

This candidate preserves the passed Marked prefix. Its maps are the original
canonical cotangent map, saturated chart reduction, and prime localization.
A full normalized kernel produces the cone and its original symbol formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open Polynomial IsLocalRing

namespace MvPolynomial

variable {k : Type u} [Field k]

private theorem homogeneous_linear_transport
    (σ : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k)
    (hσ : ∀ i : Fin 3, (σ (X i)).IsHomogeneous 1)
    {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) :
    (σ L).IsHomogeneous 1 := by
  have hspan : Submodule.span k (Set.range (X : Fin 3 → MvPolynomial (Fin 3) k)) ≤
      (homogeneousSubmodule (Fin 3) k 1).comap σ.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hσ i
  apply hspan
  rw [← homogeneousSubmodule_one_eq_span_X]
  exact hL

end MvPolynomial

namespace MvPolynomial

variable {k : Type u} [CommRing k]

/-- The polynomial shear sending `X₀` to `X₀ + a*X₁ + b*X₂` and fixing the other variables. -/
def otherShiftHom (a b : k) : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k :=
  aeval ![X 0 + C a * X 1 + C b * X 2, X 1, X 2]

theorem otherShiftHom_comp (a b : k) :
    (otherShiftHom a b).comp (otherShiftHom (-a) (-b)) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [otherShiftHom, AlgHom.comp_apply]
  ring

/-- The invertible polynomial shear whose inverse negates both coefficients. -/
def otherShift (a b : k) : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k :=
  AlgEquiv.ofAlgHom (otherShiftHom a b) (otherShiftHom (-a) (-b))
    (otherShiftHom_comp a b) (by simpa only [neg_neg] using otherShiftHom_comp (-a) (-b))

theorem otherShift_symm_X (a b : k) (i : Fin 3) :
    (otherShift a b).symm (X i) =
      ![X 0 + C (-a) * X 1 + C (-b) * X 2, X 1, X 2] i := by
  change otherShiftHom (-a) (-b) (X i) = _
  simp only [otherShiftHom, MvPolynomial.aeval_X]

theorem otherShift_symm_X_homogeneous (a b : k) (i : Fin 3) :
    ((otherShift a b).symm (X i)).IsHomogeneous 1 := by
  have h0 : ((otherShift a b).symm (X 0)).IsHomogeneous 1 := by
    rw [otherShift_symm_X]
    exact ((isHomogeneous_X k 0).add
      (isHomogeneous_C_mul_X (-a) 1)).add (isHomogeneous_C_mul_X (-b) 2)
  have h1 : ((otherShift a b).symm (X 1)).IsHomogeneous 1 := by
    rw [otherShift_symm_X]
    exact isHomogeneous_X k 1
  have h2 : ((otherShift a b).symm (X 2)).IsHomogeneous 1 := by
    rw [otherShift_symm_X]
    exact isHomogeneous_X k 2
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end MvPolynomial

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

private theorem cotangentKernel_transport
    (g g' : Fin 3 → maximalIdeal A)
    (σ : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A) ≃ₐ[IsLocalRing.ResidueField A]
      MvPolynomial (Fin 3) (IsLocalRing.ResidueField A))
    (hmap : (Ideal.cotangentPolynomialMap (maximalIdeal A) g').toRingHom =
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom.comp σ.toRingHom)
    (hσ : ∀ i : Fin 3, (σ.symm (MvPolynomial.X i)).IsHomogeneous 1)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) (hL : L.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel A g = Ideal.span {L ^ 2}) :
    ∃ L' : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A), L'.IsHomogeneous 1 ∧
      doubleLineChildCotangentKernel A g' = Ideal.span {L' ^ 2} := by
  refine ⟨σ.symm L, MvPolynomial.homogeneous_linear_transport σ.symm hσ hL, ?_⟩
  have hcomp : doubleLineChildCotangentKernel A g' =
      (doubleLineChildCotangentKernel A g).comap σ.toRingHom := by
    ext p
    change (Ideal.cotangentPolynomialMap (maximalIdeal A) g').toRingHom p = 0 ↔
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom (σ p) = 0
    rw [hmap]
    rfl
  have hspan : (Ideal.span {σ.symm L ^ 2}).map σ.toRingHom = Ideal.span {L ^ 2} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change σ (σ.symm L ^ 2) = L ^ 2
    rw [map_pow, σ.apply_symm_apply]
  rw [hcomp, hker, ← hspan]
  exact Ideal.comap_map_of_bijective σ.toRingHom σ.bijective

omit [IsLocalRing A] in
private theorem chart_degreeOne_smul (I : Ideal A) (a : A) (x : I) :
    Ideal.associatedGradedDegreeOneLinear I (a • x) =
      algebraMap A I.associatedGraded a * Ideal.associatedGradedDegreeOneLinear I x := by
  let π : reesAlgebra I →+* I.associatedGraded := Ideal.Quotient.mk I.associatedGradedIdeal
  have h : reesAlgebra.degreeOne I (a • x) =
      algebraMap A (reesAlgebra I) a * reesAlgebra.degreeOne I x := by
    apply Subtype.ext
    change Polynomial.monomial 1 (a * (x : A)) =
      Polynomial.C a * Polynomial.monomial 1 (x : A)
    exact Polynomial.C_mul_monomial.symm
  change π (reesAlgebra.degreeOne I (a • x)) =
    π (algebraMap A (reesAlgebra I) a) * π (reesAlgebra.degreeOne I x)
  rw [h, π.map_mul]

omit [IsLocalRing A] in
private theorem other_shift_of_span_pair (t v q u a b : A)
    (h : a * t + b * v = q - u) : q + (-b) * v + (-a) * t = u := by
  linear_combination -h

omit [IsLocalRing A] in
private theorem map_other_shift_of_span_pair {B : Type u} [NonAssocSemiring B]
    (f : A →+* B) (t v q u a b : A) (h : a * t + b * v = q - u) :
    f q + f (-b) * f v + f (-a) * f t = f u := by
  simpa only [map_add, map_mul] using
    congrArg f (other_shift_of_span_pair t v q u a b h)

/-- Replace the first actual generator by `g₀ + a*g₁ + b*g₂`, retaining the other two. -/
def otherShiftTriple (g : Fin 3 → maximalIdeal A) (a b : A) : Fin 3 → maximalIdeal A :=
  ![g 0 + a • g 1 + b • g 2, g 1, g 2]

theorem cotangentPolynomialMap_otherShift (g : Fin 3 → maximalIdeal A) (a b : A) :
    Ideal.cotangentPolynomialMap (maximalIdeal A) (otherShiftTriple g a b) =
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).comp
        (MvPolynomial.otherShiftHom (k := A ⧸ maximalIdeal A)
          (Ideal.Quotient.mk (maximalIdeal A) a) (Ideal.Quotient.mk (maximalIdeal A) b)) := by
  let I := maximalIdeal A
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change Ideal.cotangentPolynomialMap I (otherShiftTriple g a b) (MvPolynomial.X 0) =
      Ideal.cotangentPolynomialMap I g
        (MvPolynomial.otherShiftHom (k := A ⧸ I)
          (Ideal.Quotient.mk I a) (Ideal.Quotient.mk I b) (MvPolynomial.X 0))
    rw [MvPolynomial.otherShiftHom, MvPolynomial.aeval_X]
    change Ideal.cotangentPolynomialMap I (otherShiftTriple g a b) (MvPolynomial.X 0) =
      Ideal.cotangentPolynomialMap I g
        (MvPolynomial.X 0 + MvPolynomial.C (Ideal.Quotient.mk I a) * MvPolynomial.X 1 +
          MvPolynomial.C (Ideal.Quotient.mk I b) * MvPolynomial.X 2)
    simp only [map_add, map_mul, Ideal.cotangentPolynomialMap_C_mk,
      Ideal.cotangentPolynomialMap_X]
    change Ideal.associatedGradedDegreeOneLinear I (g 0 + a • g 1 + b • g 2) =
      Ideal.associatedGradedDegreeOneLinear I (g 0) +
        algebraMap A I.associatedGraded a * Ideal.associatedGradedDegreeOneLinear I (g 1) +
          algebraMap A I.associatedGraded b * Ideal.associatedGradedDegreeOneLinear I (g 2)
    rw [map_add, map_add, chart_degreeOne_smul, chart_degreeOne_smul]
  · simp [otherShiftTriple, MvPolynomial.otherShiftHom, AlgHom.comp_apply,
      Ideal.cotangentPolynomialMap_X]
  · simp [otherShiftTriple, MvPolynomial.otherShiftHom, AlgHom.comp_apply,
      Ideal.cotangentPolynomialMap_X]

theorem cotangentKernel_otherShift (g : Fin 3 → maximalIdeal A) (a b : A)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) (hL : L.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel A g = Ideal.span {L ^ 2}) :
    ∃ L' : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A), L'.IsHomogeneous 1 ∧
      doubleLineChildCotangentKernel A (otherShiftTriple g a b) = Ideal.span {L' ^ 2} := by
  let σ := MvPolynomial.otherShift (residue A a) (residue A b)
  have hmap : (Ideal.cotangentPolynomialMap (maximalIdeal A) (otherShiftTriple g a b)).toRingHom =
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom.comp σ.toRingHom := by
    apply RingHom.ext
    intro p
    change Ideal.cotangentPolynomialMap (maximalIdeal A) (otherShiftTriple g a b) p =
      Ideal.cotangentPolynomialMap (maximalIdeal A) g (σ p)
    rw [cotangentPolynomialMap_otherShift]
    rfl
  apply cotangentKernel_transport g (otherShiftTriple g a b) σ hmap ?_ L hL hker
  intro i
  exact MvPolynomial.otherShift_symm_X_homogeneous _ _ i

/-- The original canonical kernel is generated by one homogeneous linear square. -/
def HasLinearSquareCotangentKernel (g : Fin 3 → maximalIdeal A) : Prop :=
  ∃ L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A), L.IsHomogeneous 1 ∧
    doubleLineChildCotangentKernel A g = Ideal.span {L ^ 2}

/-- Complete the coordinate and full-kernel transport over one fixed local
ring before specializing the generators to an actual prime localization. -/
private theorem cotangentKernel_otherShift_of_coordinates
    (g g' : Fin 3 → maximalIdeal A) (a b : A)
    (h0 : (g 0 : A) + a * (g 1 : A) + b * (g 2 : A) = (g' 0 : A))
    (h1 : g 1 = g' 1) (h2 : g 2 = g' 2)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) (hL : L.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel A g = Ideal.span {L ^ 2}) :
    HasLinearSquareCotangentKernel g' := by
  have hg : otherShiftTriple g a b = g' := by
    funext i
    fin_cases i
    · apply Subtype.ext
      change (g 0 : A) + a * (g 1 : A) + b * (g 2 : A) = (g' 0 : A)
      exact h0
    · exact h1
    · exact h2
  obtain ⟨L', hL', hkernel⟩ := cotangentKernel_otherShift g a b L hL hker
  rw [hg] at hkernel
  exact ⟨L', hL', hkernel⟩

end IsLocalRing

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

theorem cotangentPolynomialMap_permutation (g : Fin 3 → maximalIdeal A)
    (e : Fin 3 ≃ Fin 3) :
    Ideal.cotangentPolynomialMap (maximalIdeal A) (fun i => g (e i)) =
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).comp
        (MvPolynomial.rename (R := A ⧸ maximalIdeal A) e) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, MvPolynomial.rename_X,
    Ideal.cotangentPolynomialMap_X, Ideal.cotangentPolynomialMap_X]

/-- Interchanging the actual plane generators transports the full canonical
linear-square kernel, retaining the actual square generator. -/
theorem cotangentKernel_swapPlane (g : Fin 3 → maximalIdeal A)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) (hL : L.IsHomogeneous 1)
    (hker : doubleLineChildCotangentKernel A g = Ideal.span {L ^ 2}) :
    ∃ L' : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A), L'.IsHomogeneous 1 ∧
      doubleLineChildCotangentKernel A ![g 2, g 1, g 0] = Ideal.span {L' ^ 2} := by
  let σ := MvPolynomial.renameEquiv (IsLocalRing.ResidueField A) (Equiv.swap (0 : Fin 3) 2)
  have hg : (fun i : Fin 3 => g ((Equiv.swap (0 : Fin 3) 2) i)) =
      ![g 2, g 1, g 0] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hp := cotangentPolynomialMap_permutation g (Equiv.swap (0 : Fin 3) 2)
  rw [hg] at hp
  have hmap : (Ideal.cotangentPolynomialMap (maximalIdeal A) ![g 2, g 1, g 0]).toRingHom =
      (Ideal.cotangentPolynomialMap (maximalIdeal A) g).toRingHom.comp σ.toRingHom := by
    apply RingHom.ext
    intro p
    change Ideal.cotangentPolynomialMap (maximalIdeal A) ![g 2, g 1, g 0] p =
      Ideal.cotangentPolynomialMap (maximalIdeal A) g (σ p)
    rw [hp]
    rfl
  apply cotangentKernel_transport g ![g 2, g 1, g 0] σ hmap ?_ L hL hker
  intro i
  change ((MvPolynomial.renameEquiv (IsLocalRing.ResidueField A)
    (Equiv.swap (0 : Fin 3) 2)).symm (MvPolynomial.X i)).IsHomogeneous 1
  rw [MvPolynomial.renameEquiv_symm]
  change (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 2).symm
    (MvPolynomial.X i : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A))).IsHomogeneous 1
  rw [MvPolynomial.rename_X]
  exact MvPolynomial.isHomogeneous_X _ _

end IsLocalRing

namespace Ideal

variable {S : Type u} [CommRing S]

/-- Perform the whole lift-difference and canonical-kernel transport at the
native prime localization of a variable source ring. The displayed triples
use exactly the original localization map and the same selected prime. -/
private theorem localTriple_linearSquareKernel_of_other_difference
    (P : Ideal S) [P.IsPrime] (t v q u : S)
    (hP : P = Ideal.span ({t, q, v} : Set S))
    (hP0 : P = Ideal.span ({t, u, v} : Set S))
    (hdiff : q - u ∈ Ideal.span ({t, v} : Set S))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hker : IsLocalRing.doubleLineChildCotangentKernel (Localization.AtPrime P)
      (Ideal.localTriple P t q v hP) = Ideal.span {L ^ 2}) :
    IsLocalRing.HasLinearSquareCotangentKernel (A := Localization.AtPrime P)
      (Ideal.localTriple P t u v hP0) := by
  let B : Type u := Localization.AtPrime P
  let loc : S →+* B := algebraMap S B
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hdiff
  have hcoord : loc q + loc (-b) * loc v + loc (-a) * loc t = loc u :=
    IsLocalRing.map_other_shift_of_span_pair (A := S) (B := B) loc t v q u a b hab
  let g := Ideal.localTriple P t q v hP
  let g0 := Ideal.localTriple P t u v hP0
  exact IsLocalRing.cotangentKernel_otherShift_of_coordinates g g0
    (loc (-b)) (loc (-a)) hcoord rfl rfl L hL hker

end Ideal

namespace Polynomial

variable {P R : Type u} [CommRing P] [CommRing R]

/-- Construct the quotient comparison and its original-polynomial formula in
one fixed native polynomial family, before substituting nested coefficient rings. -/
private theorem exists_original_quotientCone_equiv
    (e : P ≃+* R[X]) (p : P) (x : R) (he : e p = Polynomial.C x) :
    ∃ E : P ⧸ Ideal.span {p} ≃+* Polynomial.quotientCone x,
      ∀ q : P, E (Ideal.Quotient.mk (Ideal.span {p}) q) =
        Polynomial.quotientConeMk x (e q) := by
  let I : Ideal P := Ideal.span {p}
  let J : Ideal R[X] := Ideal.span {Polynomial.C x}
  let : I.IsTwoSided := ⟨fun b ha => mul_comm b _ ▸ I.smul_mem _ ha⟩
  let : J.IsTwoSided := ⟨fun b ha => mul_comm b _ ▸ J.smul_mem _ ha⟩
  have hJ : J = I.map e.toRingHom := by
    change Ideal.span {Polynomial.C x} = (Ideal.span {p}).map e.toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun y : R[X] => Ideal.span {y}) he.symm
  let E : P ⧸ I ≃+* Polynomial.quotientCone x :=
    Ideal.quotientEquiv (R := P) (S := R[X]) I J e hJ
  refine ⟨E, ?_⟩
  intro q
  exact Ideal.quotientEquiv_mk (R := P) (S := R[X]) I J e hJ q

end Polynomial

namespace MvPolynomial

variable (k : Type u) [CommRing k]

/-- The two inner variables retain the square and other coordinates. -/
def doubleLinePlaneVariablesEquiv : MvPolynomial (Fin 2) k ≃ₐ[k] k[X][X] :=
  (finSuccEquiv k 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv k (Fin 1)))

theorem doubleLinePlaneVariablesEquiv_zero :
    doubleLinePlaneVariablesEquiv k (X 0) = (Polynomial.X : k[X][X]) := by
  change Polynomial.map (uniqueAlgEquiv k (Fin 1)).toRingHom
    (finSuccEquiv k 1 (X 0)) = _
  rw [finSuccEquiv_X_zero, Polynomial.map_X]

theorem doubleLinePlaneVariablesEquiv_one :
    doubleLinePlaneVariablesEquiv k (X 1) = Polynomial.C (Polynomial.X : k[X]) := by
  change Polynomial.map (uniqueAlgEquiv k (Fin 1)).toRingHom
    (finSuccEquiv k 1 (X (0 : Fin 1).succ)) = _
  rw [finSuccEquiv_X_succ, Polynomial.map_C]
  change Polynomial.C (uniqueAlgEquiv k (Fin 1) (X (0 : Fin 1))) = _
  rw [uniqueAlgEquiv_apply, MvPolynomial.eval₂_X]

/-- Regroup the original variables as other, square, and outer parameter. -/
def doubleLineVariablesEquiv : MvPolynomial (Fin 3) k ≃ₐ[k] k[X][X][X] :=
  (renameEquiv k (Equiv.swap (0 : Fin 3) 2)).trans
    ((finSuccEquiv k 2).trans (Polynomial.mapAlgEquiv (doubleLinePlaneVariablesEquiv k)))

theorem doubleLineVariablesEquiv_other :
    doubleLineVariablesEquiv k (X 0) = Polynomial.C (Polynomial.C (Polynomial.X : k[X])) := by
  change Polynomial.map (doubleLinePlaneVariablesEquiv k).toRingHom
    (finSuccEquiv k 2 (renameEquiv k (Equiv.swap (0 : Fin 3) 2) (X 0))) = _
  rw [renameEquiv_apply, rename_X, Equiv.swap_apply_left]
  change Polynomial.map (doubleLinePlaneVariablesEquiv k).toRingHom
    (finSuccEquiv k 2 (X (1 : Fin 2).succ)) = _
  rw [finSuccEquiv_X_succ, Polynomial.map_C]
  change Polynomial.C (doubleLinePlaneVariablesEquiv k (X 1)) = _
  rw [doubleLinePlaneVariablesEquiv_one]

theorem doubleLineVariablesEquiv_square :
    doubleLineVariablesEquiv k (X 1) = Polynomial.C (Polynomial.X : k[X][X]) := by
  change Polynomial.map (doubleLinePlaneVariablesEquiv k).toRingHom
    (finSuccEquiv k 2 (renameEquiv k (Equiv.swap (0 : Fin 3) 2) (X 1))) = _
  rw [renameEquiv_apply, rename_X,
    Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0)
      (by decide : (1 : Fin 3) ≠ 2)]
  change Polynomial.map (doubleLinePlaneVariablesEquiv k).toRingHom
    (finSuccEquiv k 2 (X (0 : Fin 2).succ)) = _
  rw [finSuccEquiv_X_succ, Polynomial.map_C]
  change Polynomial.C (doubleLinePlaneVariablesEquiv k (X 0)) = _
  rw [doubleLinePlaneVariablesEquiv_zero]

theorem doubleLineVariablesEquiv_parameter :
    doubleLineVariablesEquiv k (X 2) = (Polynomial.X : k[X][X][X]) := by
  change Polynomial.map (doubleLinePlaneVariablesEquiv k).toRingHom
    (finSuccEquiv k 2 (renameEquiv k (Equiv.swap (0 : Fin 3) 2) (X 2))) = _
  rw [renameEquiv_apply, rename_X, Equiv.swap_apply_right,
    finSuccEquiv_X_zero, Polynomial.map_X]

theorem doubleLineVariablesEquiv_coefficient (a : k) :
    doubleLineVariablesEquiv k (C a) = Polynomial.C (Polynomial.C (Polynomial.C a)) :=
  (doubleLineVariablesEquiv k).commutes a

/-- The original variable equivalence retains the displayed square relation. -/
theorem doubleLineVariablesEquiv_square_relation :
    doubleLineVariablesEquiv k (X 1 ^ 2) =
      Polynomial.C ((Polynomial.X : k[X][X]) ^ 2) := by
  calc
    doubleLineVariablesEquiv k (X 1 ^ 2) =
        (doubleLineVariablesEquiv k (X 1)) ^ 2 := map_pow _ _ _
    _ = (Polynomial.C (Polynomial.X : k[X][X])) ^ 2 :=
      congrArg (fun p : k[X][X][X] => p ^ 2) (doubleLineVariablesEquiv_square k)
    _ = Polynomial.C ((Polynomial.X : k[X][X]) ^ 2) := (map_pow Polynomial.C _ _).symm

/-- The original surjective map factors through the same native polynomial
cone. The target needs only the semiring structure carried by that map. -/
theorem exists_doubleLineConeEquiv {G : Type u} [Semiring G]
    (f : MvPolynomial (Fin 3) k →+* G) (hf : Function.Surjective f)
    (hk : RingHom.ker f = Ideal.span {(X 1 : MvPolynomial (Fin 3) k) ^ 2}) :
    ∃ E : G ≃+* Polynomial.quotientCone ((Polynomial.X : k[X][X]) ^ 2),
      ∀ p : MvPolynomial (Fin 3) k, E (f p) =
        Polynomial.quotientConeMk ((Polynomial.X : k[X][X]) ^ 2)
          (doubleLineVariablesEquiv k p) := by
  obtain ⟨e, he⟩ := Polynomial.exists_original_quotientCone_equiv
    (P := MvPolynomial (Fin 3) k) (R := k[X][X])
    (doubleLineVariablesEquiv k).toRingEquiv (X 1 ^ 2) ((Polynomial.X : k[X][X]) ^ 2)
    (doubleLineVariablesEquiv_square_relation k)
  let E : G ≃+* Polynomial.quotientCone ((Polynomial.X : k[X][X]) ^ 2) :=
    (f.quotientKerEquivOfSurjective hf).symm.trans ((Ideal.quotEquivOfEq hk).trans e)
  refine ⟨E, ?_⟩
  intro p
  calc
    E (f p) = e ((Ideal.quotEquivOfEq hk) (Ideal.Quotient.mk (RingHom.ker f) p)) := by
      change e ((Ideal.quotEquivOfEq hk)
        ((f.quotientKerEquivOfSurjective hf).symm (f p))) = _
      exact congrArg (fun x => e ((Ideal.quotEquivOfEq hk) x))
        (RingHom.quotientKerEquivOfSurjective_symm_apply hf p)
    _ = e (Ideal.Quotient.mk (Ideal.span {(X 1 : MvPolynomial (Fin 3) k) ^ 2}) p) :=
      congrArg e (Ideal.quotEquivOfEq_mk hk p)
    _ = _ := he p

end MvPolynomial

namespace Localization.Away.SaturatedChart.DoubleLinePresentation

variable {A : Type u} [CommRing A] [IsLocalRing A]

private theorem nonempty_of_canonical_equiv (t s z : maximalIdeal A)
    (E : (maximalIdeal A).associatedGraded ≃+*
      Polynomial.quotientCone ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2))
    (hE : ∀ p : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A),
      E ((Ideal.cotangentPolynomialMap (maximalIdeal A) ![s, z, t]).toRingHom p) =
        Polynomial.quotientConeMk ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2)
          (MvPolynomial.doubleLineVariablesEquiv (IsLocalRing.ResidueField A) p)) :
    Nonempty (DoubleLinePresentation t s z) := by
  let I := maximalIdeal A
  let g : Fin 3 → I := ![s, z, t]
  let f : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A) →+* I.associatedGraded :=
    (Ideal.cotangentPolynomialMap I g).toRingHom
  have hE' (p : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) : E (f p) =
      Polynomial.quotientConeMk ((X : (IsLocalRing.ResidueField A)[X][X]) ^ 2)
        (MvPolynomial.doubleLineVariablesEquiv (IsLocalRing.ResidueField A) p) := hE p
  have hX (i : Fin 3) : f (MvPolynomial.X i) =
      Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I (g i)) :=
    Ideal.cotangentPolynomialMap_X I g i
  refine ⟨⟨E, ?_, ?_, ?_, ?_⟩⟩
  · have h := hE' (MvPolynomial.X 2)
    rw [hX, MvPolynomial.doubleLineVariablesEquiv_parameter] at h
    exact h
  · have h := hE' (MvPolynomial.X 0)
    rw [hX, MvPolynomial.doubleLineVariablesEquiv_other] at h
    exact h
  · have h := hE' (MvPolynomial.X 1)
    rw [hX, MvPolynomial.doubleLineVariablesEquiv_square] at h
    exact h
  · intro a
    have hC : f (MvPolynomial.C (residue A a)) =
        Ideal.Quotient.mk I.associatedGradedIdeal (algebraMap A (reesAlgebra I) a) :=
      Ideal.cotangentPolynomialMap_C_mk I g a
    have h := hE' (MvPolynomial.C (residue A a))
    rw [hC, MvPolynomial.doubleLineVariablesEquiv_coefficient] at h
    exact h

/-- The normalized full canonical kernel produces the actual cone equivalence,
including every original symbol and the original coefficient map. -/
theorem nonempty_of_kernel (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2}) :
    Nonempty (DoubleLinePresentation t s z) := by
  let k := IsLocalRing.ResidueField A
  let I := maximalIdeal A
  let g : Fin 3 → I := ![s, z, t]
  let f : MvPolynomial (Fin 3) k →+* I.associatedGraded :=
    (Ideal.cotangentPolynomialMap I g).toRingHom
  have hrange : Set.range (fun i : Fin 3 => (g i : A)) =
      ({(s : A), (z : A), (t : A)} : Set A) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [g]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hgens : Ideal.span (Set.range fun i : Fin 3 => (g i : A)) = I := by
    rw [hrange, Set.pair_comm (z : A) (t : A), Set.insert_comm]
    exact hgen.symm
  have hf : Function.Surjective f :=
    Ideal.cotangentPolynomialMap_surjective_of_cotangent_span I g
      (Ideal.cotangent_span_of_ideal_span I g hgens)
  have hk : RingHom.ker f =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) k) ^ 2} := hker
  obtain ⟨E, hE⟩ := MvPolynomial.exists_doubleLineConeEquiv k f hf hk
  exact nonempty_of_canonical_equiv t s z E hE

/-- Choose the proved original-symbol presentation without unfolding its
quotient construction at each later concrete chart use. -/
def ofKernel (t s z : maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3)
        (IsLocalRing.ResidueField A)) ^ 2}) : DoubleLinePresentation t s z :=
  Classical.choice (nonempty_of_kernel t s z hgen hker)

end Localization.Away.SaturatedChart.DoubleLinePresentation

namespace IsLocalRing

open Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The marked successor provides its own actual normalized cone, rather than
requiring a new cone presentation as a continuation premise. -/
def MarkedCubic.presentation {t : maximalIdeal A} (M : MarkedCubic t) :
    DoubleLinePresentation t M.other M.square :=
  DoubleLinePresentation.ofKernel t M.other M.square M.generates M.tangent

/-- The aligned triple-entry stage provides its own original normalized cone. -/
def TripleEntryData.presentation {t u w : maximalIdeal A} (T : TripleEntryData t u w) :
    DoubleLinePresentation t u w :=
  DoubleLinePresentation.ofKernel t u w T.generates T.tangent

end IsLocalRing

namespace IsLocalRing

open Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The genuine opposite chart of a marked ring uses the same canonical cone. -/
def MarkedCubic.oppositePresentation {t : maximalIdeal A} (M : MarkedCubic t) :
    DoubleLinePresentation M.other t M.square := by
  apply DoubleLinePresentation.ofKernel
  · simpa only [Set.insert_comm] using M.generates
  · have h := cotangentKernel_planeChange ![M.other, M.square, t] 0 1 1 0
      (by simp) M.tangent
    simpa only [planeChangeTriple_triple, zero_smul, one_smul, zero_add, add_zero] using h

/-- The first triple-entry stage also supplies the cone on its genuine opposite chart. -/
def TripleEntryData.oppositePresentation {t u w : maximalIdeal A} (T : TripleEntryData t u w) :
    DoubleLinePresentation u t w := by
  apply DoubleLinePresentation.ofKernel
  · simpa only [Set.insert_comm] using T.generates
  · have h := cotangentKernel_planeChange ![u, w, t] 0 1 1 0 (by simp) T.tangent
    simpa only [planeChangeTriple_triple, zero_smul, one_smul, zero_add, add_zero] using h

end IsLocalRing

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

theorem fractionElement_recenter (t s : maximalIdeal A) (α : A) :
    fractionElement (maximalIdeal A) t (s - α • t) =
      fractionElement (maximalIdeal A) t s -
        algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) α := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  apply exceptional_pow_mul_injective (maximalIdeal A) (t : A) 1
  simp only [pow_one]
  rw [fractionElement_mul, mul_sub, fractionElement_mul]
  simp only [Submodule.coe_sub, Submodule.coe_smul, smul_eq_mul, map_sub, map_mul]
  ring

/-- The actual reduced quotient, with the original chart and coefficient law fixed. -/
structure ReducedDoubleLineChart (t s z : maximalIdeal A) where
  /-- The original chart reduction map to the residue-field polynomial line. -/
  map : saturatedChart A (maximalIdeal A) (t : A) →+* (IsLocalRing.ResidueField A)[X]
  surjective : Function.Surjective map
  kernel : RingHom.ker map = Ideal.span
    ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A),
      fractionElement (maximalIdeal A) t z} : Set (saturatedChart A (maximalIdeal A) (t : A)))
  other : map (fractionElement (maximalIdeal A) t s) = X
  coefficient : ∀ a : A,
    map (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a) = Polynomial.C (residue A a)

/-- The reduced chart and its original scalar laws supplied by the double-line presentation. -/
def DoubleLinePresentation.reducedChart {t s z : maximalIdeal A}
    (E : DoubleLinePresentation t s z) : ReducedDoubleLineChart t s z :=
  ⟨E.reduction, E.reduction_surjective, E.reduction_kernel, E.reduction_other,
    E.reduction_coefficient⟩

namespace ReducedDoubleLineChart

variable {t s z : maximalIdeal A} (D : ReducedDoubleLineChart t s z)

/-- Recenter the original chart at `s - α*t` by translating its residue polynomial variable. -/
def recenter (α : A) : ReducedDoubleLineChart t (s - α • t) z where
  map := (Polynomial.algEquivAevalXAddC (residue A α)).toRingHom.comp D.map
  surjective := (Polynomial.algEquivAevalXAddC (residue A α)).surjective.comp D.surjective
  kernel := by
    exact (RingHom.ker_comp_of_injective D.map
      (f := (Polynomial.algEquivAevalXAddC (residue A α)).toRingEquiv.toRingHom)
      (Polynomial.algEquivAevalXAddC (residue A α)).injective).trans D.kernel
  other := by
    rw [RingHom.comp_apply, fractionElement_recenter, map_sub, D.other, D.coefficient]
    change (Polynomial.algEquivAevalXAddC (residue A α)) (X - Polynomial.C (residue A α)) = X
    change (X - Polynomial.C (residue A α)).comp (X + Polynomial.C (residue A α)) = X
    simp
  coefficient := by
    intro a
    rw [RingHom.comp_apply, D.coefficient]
    exact (Polynomial.algEquivAevalXAddC (residue A α)).commutes (residue A a)

theorem recenter_prime (α : A) :
    (Ideal.span {(X : (IsLocalRing.ResidueField A)[X])}).comap (D.recenter α).map =
      (Ideal.span {X - Polynomial.C (residue A α)}).comap D.map := by
  have hX : Ideal.span ({X} : Set (IsLocalRing.ResidueField A)[X]) =
      RingHom.ker (Polynomial.evalRingHom (0 : IsLocalRing.ResidueField A)) := by
    simpa only [map_zero, sub_zero] using
      (Polynomial.ker_evalRingHom (0 : IsLocalRing.ResidueField A)).symm
  rw [hX, ← Polynomial.ker_evalRingHom]
  ext x
  change (((D.map x).comp (X + Polynomial.C (residue A α))).eval 0 = 0) ↔
    (D.map x).eval (residue A α) = 0
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]

theorem centered_prime_span
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A)))
    (hP : P = (Ideal.span {X}).comap D.map) :
    P = Ideal.span
      ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A),
        fractionElement (maximalIdeal A) t s,
        fractionElement (maximalIdeal A) t z} :
          Set (saturatedChart A (maximalIdeal A) (t : A))) := by
  have h := hP.trans (Ideal.reduced_doubleLine_child_prime_eq_span D.map D.surjective
    (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A))
    (fractionElement (maximalIdeal A) t z) (fractionElement (maximalIdeal A) t s)
    X D.kernel D.other)
  refine h.trans ?_
  simp only [Ideal.span_insert]
  exact congrArg (fun J => Ideal.span
    ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)} :
      Set (saturatedChart A (maximalIdeal A) (t : A))) ⊔ J) (sup_comm _ _)

/-- The localized original parameter and two fractions at the prime over the origin. -/
def centeredTriple
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {X}).comap D.map) :
    Fin 3 → maximalIdeal (Localization.AtPrime P) :=
  Ideal.localTriple P
    (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A))
    (fractionElement (maximalIdeal A) t s) (fractionElement (maximalIdeal A) t z)
    (D.centered_prime_span P hP)

theorem centered_residue_bijective
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {X}).comap D.map) :
    ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (t : A) P),
      let _ := hlocal
      Function.Bijective (IsLocalRing.ResidueField.map (R := A) (S := Localization.AtPrime P)
        (localizedChartMap (maximalIdeal A) (t : A) P)) := by
  let φ := (Polynomial.evalRingHom (0 : IsLocalRing.ResidueField A)).comp D.map
  have hφ : φ.comp (algebraMap A (saturatedChart A (maximalIdeal A) (t : A))) = residue A := by
    ext a
    change (D.map (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) a)).eval 0 = residue A a
    rw [D.coefficient, Polynomial.eval_C]
  have hPker : P = RingHom.ker φ := by
    have hX : Ideal.span ({X} : Set (IsLocalRing.ResidueField A)[X]) =
        RingHom.ker (Polynomial.evalRingHom (0 : IsLocalRing.ResidueField A)) := by
      simpa only [map_zero, sub_zero] using
        (Polynomial.ker_evalRingHom (0 : IsLocalRing.ResidueField A)).symm
    rw [hP, hX]
    rfl
  exact localizedChartMap_residue_bijective_of_point_kernel (maximalIdeal A) (t : A) P φ hφ hPker

end ReducedDoubleLineChart

end Localization.Away.SaturatedChart

namespace Localization.Away.SaturatedChart.CubicCoefficients

variable {A : Type u} [CommRing A] [IsLocalRing A]

theorem residueCubic_coeff_two (C : CubicCoefficients A) :
    C.residueCubic.coeff 2 = residue A C.a2 := by
  simp [residueCubic, IsLocalRing.residueBinaryCubic]

end Localization.Away.SaturatedChart.CubicCoefficients

namespace Localization.Away.SaturatedChart.CubicCoefficients

variable {A : Type u} [CommRing A] [IsLocalRing A]

theorem residueCubic_coeff_three (C : CubicCoefficients A) :
    C.residueCubic.coeff 3 = residue A C.a3 := by
  simp [residueCubic, IsLocalRing.residueBinaryCubic]

end Localization.Away.SaturatedChart.CubicCoefficients

namespace Localization.Away.SaturatedChart.ReducedDoubleLineChart

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {t s z : maximalIdeal A} (D : ReducedDoubleLineChart t s z)

theorem prime_span (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A)))
    (hP : P = (Ideal.span {q}).comap D.map) :
    P = Ideal.span
      ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A), Q,
        fractionElement (maximalIdeal A) t z} :
          Set (saturatedChart A (maximalIdeal A) (t : A))) := by
  have h := hP.trans (Ideal.reduced_doubleLine_child_prime_eq_span D.map D.surjective
    (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A))
    (fractionElement (maximalIdeal A) t z) Q q D.kernel hQ)
  refine h.trans ?_
  simp only [Ideal.span_insert]
  exact congrArg (fun J => Ideal.span
    ({algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)} :
      Set (saturatedChart A (maximalIdeal A) (t : A))) ⊔ J) (sup_comm _ _)

/-- The localized triple formed by the original parameter, a chosen lift of `q`, and `z/t`. -/
def primeTriple (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map) :
    Fin 3 → maximalIdeal (Localization.AtPrime P) :=
  Ideal.localTriple P
    (algebraMap A (saturatedChart A (maximalIdeal A) (t : A)) (t : A)) Q
    (fractionElement (maximalIdeal A) t z) (D.prime_span Q q hQ P hP)

theorem child_sq_dvd [IsNoetherianRing A] (F : CubicRelation t s z)
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) :
    q ^ 2 ∣ F.coefficients.residueCubic := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let : IsNoetherianRing S := saturatedChart_isNoetherian (maximalIdeal A) (t : A)
  let φ : A →+* S := algebraMap A S
  let τ := φ (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  let C := F.coefficients
  let H := φ C.a0 + φ C.a1 * U + φ C.a2 * U ^ 2 + φ C.a3 * U ^ 3
  let l := φ C.b0 + φ C.b1 * U + φ C.b2 * U ^ 2 +
    φ C.c0 * V + φ C.c1 * U * V + φ C.d0 * V ^ 2
  obtain ⟨r, hr⟩ := F.divided
  have hφ (a : A) : D.map (φ a) = Polynomial.C (residue A a) := D.coefficient a
  have hU : D.map U = X := D.other
  have hH : D.map H = F.coefficients.residueCubic := by
    dsimp only [H, CubicCoefficients.residueCubic]
    simp only [map_add, map_mul, map_pow, hφ, hU, IsLocalRing.residueBinaryCubic]
    ring
  exact Ideal.sq_dvd_of_actual_doubleLine_child D.map D.surjective τ V Q H l r q
    F.coefficients.residueCubic D.kernel hQ hH hr P hP hd hsing
    (D.primeTriple Q q hQ P hP) rfl rfl rfl L hL hCaseII

theorem centered_kernel_of_linear_prime
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (α : A) (hq : q = X - Polynomial.C (residue A α))
    (hP0 : P = (Ideal.span {X}).comap (D.recenter α).map)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) :
    IsLocalRing.HasLinearSquareCotangentKernel (A := Localization.AtPrime P)
      ((D.recenter α).centeredTriple P hP0) := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let τ := algebraMap A S (t : A)
  let V := fractionElement (maximalIdeal A) t z
  let U0 := fractionElement (maximalIdeal A) t (s - α • t)
  have hU0 : D.map U0 = q := by
    dsimp only [U0]
    rw [fractionElement_recenter, map_sub, D.other, D.coefficient, hq]
  have hdiff : Q - U0 ∈ Ideal.span ({τ, V} : Set S) := by
    rw [← D.kernel]
    change D.map (Q - U0) = 0
    rw [map_sub, hQ, hU0, sub_self]
  exact Ideal.localTriple_linearSquareKernel_of_other_difference P τ V Q U0
    (D.prime_span Q q hQ P hP) ((D.recenter α).centered_prime_span P hP0)
    hdiff L hL hCaseII

end Localization.Away.SaturatedChart.ReducedDoubleLineChart

namespace Localization.Away.SaturatedChart.ReducedDoubleLineChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {t s z : maximalIdeal A} (D : ReducedDoubleLineChart t s z)

/-- The original repeated origin is the actual continuing prime. Repeatedness
of the actual child is obtained from its divided equation and canonical kernel. -/
theorem prime_eq_X_of_zero_low_coefficients (F : CubicRelation t s z)
    (h0 : residue A F.coefficients.a0 = 0) (h1 : residue A F.coefficients.a1 = 0)
    (hn : F.coefficients.residueCubic ≠ 0)
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (hq : Irreducible q) (hm : q.Monic)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) : q = X := by
  have hX : (X : (IsLocalRing.ResidueField A)[X]) ^ 2 ∣ F.coefficients.residueCubic := by
    refine ⟨C (residue A F.coefficients.a2) + C (residue A F.coefficients.a3) * X, ?_⟩
    dsimp only [CubicCoefficients.residueCubic, IsLocalRing.residueBinaryCubic]
    rw [h0, h1, map_zero]
    ring
  have hqdiv := D.child_sq_dvd F Q q hQ P hP hd hsing L hL hCaseII
  exact Polynomial.eq_of_monic_of_associated hm Polynomial.monic_X
    (Polynomial.associated_of_irreducible_sq_dvd_cubic hn
      (IsLocalRing.residueBinaryCubic_natDegree_le _ _ _ _)
      hq Polynomial.irreducible_X hqdiv hX)

omit [IsNoetherianRing A] in
/-- Changing a lift of the same actual origin changes its cotangent coordinate
only by the displayed exceptional and square coordinates. -/
theorem centered_kernel_of_origin
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q) (hq : q = X)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hP0 : P = (Ideal.span {X}).comap D.map)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) :
    IsLocalRing.HasLinearSquareCotangentKernel (A := Localization.AtPrime P)
      (D.centeredTriple P hP0) := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let τ := algebraMap A S (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  have hdiff : Q - U ∈ Ideal.span ({τ, V} : Set S) := by
    rw [← D.kernel]
    change D.map (Q - U) = 0
    rw [map_sub, hQ, D.other, hq, sub_self]
  exact Ideal.localTriple_linearSquareKernel_of_other_difference P τ V Q U
    (D.prime_span Q q hQ P hP) (D.centered_prime_span P hP0) hdiff L hL hCaseII

end Localization.Away.SaturatedChart.ReducedDoubleLineChart

