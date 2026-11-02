/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.CoefficientComparison
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.HyperplaneSupport
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.VanishingDimension
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Ample
public import Aglib.Topology.KrullDimension.IrreducibleClosed

/-!
# The actual support dimension is the native Hilbert-polynomial degree

For a nonzero coherent coefficient on projective space over an infinite
field, its original support dimension equals the degree of its original
Hilbert polynomial. The lower bound is induction on a finite dimension
witness in that support. A native reduced integral closed subscheme carries
that witness. An ample hyperplane has a closed zero there, and the actual
local principal quotient supplies the next smaller support witness in the
original hyperplane cokernel. Its polynomial is the proved finite difference.

No support-degree equality, polarization law, replacement cohomology model
or intersection-theory datum is supplied as a premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem natDegree_nonzero_difference_lt (P : ℚ[X])
    (hD : P.comp (Polynomial.X + 1) - P ≠ 0) :
    (P.comp (Polynomial.X + 1) - P).natDegree < P.natDegree := by
  have hP : P ≠ 0 := by
    intro h
    exact hD (by rw [h]; simp)
  have hd : (P.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree = P.degree := by
    rw [Polynomial.degree_comp (by rw [Polynomial.degree_X_add_C]; exact zero_lt_one),
      Polynomial.degree_X_add_C, mul_one]
  have hl : (P.comp (Polynomial.X + Polynomial.C (1 : ℚ))).leadingCoeff = P.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp (by
      rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
  have h := Polynomial.degree_sub_lt_right hd hP hl
  rw [Polynomial.degree_eq_natDegree hP] at h
  exact (Polynomial.natDegree_lt_iff_degree_lt hD).mpr (by simpa only [Polynomial.C_1] using h)

private theorem exists_integral_closed_subscheme_dim_ge
    {X : Scheme.{u}} (S : Set X) (hS : IsClosed S) (d : ℕ)
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim S) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsClosedImmersion j ∧ IsIntegral Z ∧
      Set.range j ⊆ S ∧ (d : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  obtain ⟨B, hBsub, hBdim⟩ :=
    exists_irreducibleClosed_subset_topologicalKrullDim_ge S hS d hd
  let W : TopologicalSpace.Closeds X := ⟨B, B.isClosed⟩
  let I := Scheme.IdealSheafData.vanishingIdeal W
  have hsupp : I.support = W := rfl
  have hrad : I.radical = I := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, hsupp]
  let Z := I.subscheme
  let j : Z ⟶ X := I.subschemeι
  let : IsReduced Z := Scheme.IdealSheafData.subscheme_reduced_of_radical I hrad
  have hrange : Set.range j = (B : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
    rfl
  let e : Z ≃ₜ B := j.isClosedEmbedding.isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr hrange)
  let : IrreducibleSpace B := Subtype.irreducibleSpace B.isIrreducible
  let : IrreducibleSpace Z := e.irreducibleSpace_iff.mpr inferInstance
  let : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  refine ⟨Z, j, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hrange]
    exact hBsub
  · exact hBdim.trans_eq (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm

/-- A hyperplane section retains a support-dimension witness one shorter
in its original cokernel. This lower bound needs no monomorphism premise. -/
theorem le_supportDimension_cokernel_hyperplane
    (k : Type u) [Field k] (ι : Type u) [Finite ι]
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType _ F)
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (support F))
    (s : Γ(twistingSheaf k ι 1, ⊤)) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDim
      (support (cokernel ((twistingTensorZeroIso k ι).inv.app F ≫
        (twistingTensorMultiply k ι 1 0 s).app F))) := by
  obtain ⟨Z, j, hj, hZ, hsub, hdimZ⟩ := exists_integral_closed_subscheme_dim_ge
    (support F) (isClosed_support_of_affineLocallyFiniteType hF) (d + 1) hd
  let : IsClosedImmersion j := hj
  let : IsIntegral Z := hZ
  let p := j ≫ ProjectiveSpace.toSpec k ι
  let : IsProper p := inferInstance
  let L := pullbackLineBundle j (twistingLineBundle k ι 1)
  let t := Nonvanishing.pullbackSection j (twistingSheaf k ι 1) s
  have hL : L.IsAmple :=
    (twistingLineBundle_one_isAmple k ι).pullback_of_isAffineHom j
  have hpos : 0 < topologicalKrullDim Z :=
    (show (0 : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) by
      exact_mod_cast Nat.zero_lt_succ d).trans_le hdimZ
  obtain ⟨x, hxzero, hxclosed⟩ := hL.exists_closed_zero_of_pos_dimension p t hpos
  have hvan := topologicalKrullDim_le_vanishingDimension_add_one_of_closed_zero
    k p L t x hxclosed hxzero
  let V : Set Z := (nonvanishingOpen L t : Set Z)ᶜ
  have hdV : (d : WithBot ℕ∞) ≤ topologicalKrullDim V := by
    by_contra h
    have hsmall : topologicalKrullDim V + 1 ≤ (d : ℕ) :=
      ENat.WithBot.add_one_le_natCast_iff.mpr (lt_of_not_ge h)
    have hbad : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) :=
      hdimZ.trans (hvan.trans hsmall)
    exact Nat.not_succ_le_self d (by exact_mod_cast hbad)
  let C := cokernel ((twistingTensorZeroIso k ι).inv.app F ≫
    (twistingTensorMultiply k ι 1 0 s).app F)
  have hsupport : support C =
      support F ∩ (nonvanishingOpen (twistingLineBundle k ι 1) s : Set (ProjectiveSpace k ι))ᶜ :=
    support_cokernel_twistingTensorMultiply k ι 1 s F hF
  have hmaps : ∀ y : V, j y.1 ∈ support C := by
    intro y
    rw [hsupport]
    refine ⟨hsub ⟨y.1, rfl⟩, ?_⟩
    have hy : y.1 ∉ nonvanishingOpen L t := y.2
    have he : nonvanishingOpen L t =
        j ⁻¹ᵁ nonvanishingOpen (twistingLineBundle k ι 1) s :=
      Nonvanishing.nonvanishingOpen_pullback j (twistingLineBundle k ι 1) s
    exact (congrArg (fun U : Z.Opens => y.1 ∉ U) he).mp hy
  have he : Topology.IsEmbedding (fun y : V => j y.1) :=
    j.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  exact hdV.trans (he.codRestrict (support C) hmaps).isInducing.topologicalKrullDim_le

variable (k : Type u) [Field k] [Infinite k] (ι : Type u)

/-- Every finite support-dimension witness is bounded by the actual
Hilbert-polynomial degree, by the original hyperplane recurrence. -/
theorem le_natDegree_projectiveHilbertPolynomial_of_supportDimension_ge
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℕ)
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType _ F)
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim (support F)) :
    d ≤ (projectiveHilbertPolynomial k ι F).natDegree := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  induction d generalizing F with
  | zero => exact Nat.zero_le _
  | succ d ih =>
    obtain ⟨s, hm, hpoly⟩ := exists_mono_hyperplane_hilbertDifference k ι n e F hF
    let ν := (twistingTensorZeroIso k ι).inv.app F ≫
      (twistingTensorMultiply k ι 1 0 s).app F
    let : Mono ν := hm
    let C := cokernel ν
    have hC : affineLocallyFiniteType (ProjectiveSpace k ι) C :=
      (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel ν hF
        (twistingTensor_affineLocallyFiniteType k ι 1 F hF)
    have hdC : (d : WithBot ℕ∞) ≤ topologicalKrullDim (support C) :=
      le_supportDimension_cokernel_hyperplane k ι F hF d hd s
    have hdegC := ih C hC hdC
    have hCne : projectiveHilbertPolynomial k ι C ≠ 0 := by
      intro hp
      have hzero := isZero_of_projectiveHilbertPolynomial_eq_zero k ι n e hC hp
      have hempty := (support_eq_empty_iff C).mpr hzero
      obtain ⟨T, _⟩ := exists_irreducibleClosed_topologicalKrullDim_ge d hdC
      obtain ⟨x, _⟩ := T.isIrreducible.nonempty
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) x.1 x.2
    change projectiveHilbertPolynomial k ι C =
      (projectiveHilbertPolynomial k ι F).comp (Polynomial.X + 1) -
        projectiveHilbertPolynomial k ι F at hpoly
    have hD : (projectiveHilbertPolynomial k ι F).comp (Polynomial.X + 1) -
        projectiveHilbertPolynomial k ι F ≠ 0 := by rwa [← hpoly]
    have hlt := natDegree_nonzero_difference_lt (projectiveHilbertPolynomial k ι F) hD
    rw [← hpoly] at hlt
    exact Nat.succ_le_of_lt (hdegC.trans_lt hlt)

/-- The support dimension of a nonzero coherent module is exactly the
natural degree of its original projective Hilbert polynomial. -/
theorem topologicalKrullDim_support_eq_natDegree_projectiveHilbertPolynomial
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType _ F) (hne : ¬ IsZero F) :
    topologicalKrullDim (support F) =
      ((projectiveHilbertPolynomial k ι F).natDegree : WithBot ℕ∞) := by
  have hP : projectiveHilbertPolynomial k ι F ≠ 0 := fun h =>
    hne (isZero_of_projectiveHilbertPolynomial_eq_zero k ι n e hF h)
  apply le_antisymm
  · by_contra h
    have hd : (((projectiveHilbertPolynomial k ι F).natDegree + 1 : ℕ) : WithBot ℕ∞) ≤
        topologicalKrullDim (support F) := ENat.WithBot.add_one_le_iff.mpr (lt_of_not_ge h)
    exact Nat.not_succ_le_self _
      (le_natDegree_projectiveHilbertPolynomial_of_supportDimension_ge k ι n e _ F hF hd)
  · by_contra h
    have hc := coeff_projectiveHilbertPolynomial_eq_zero_of_supportDimension_lt
      k ι n e F hF (projectiveHilbertPolynomial k ι F).natDegree (lt_of_not_ge h)
    exact (Polynomial.leadingCoeff_ne_zero.mpr hP) (by
      simpa only [Polynomial.coeff_natDegree] using hc)

end AlgebraicGeometry.Scheme.Cohomology
