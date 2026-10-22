/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Relations
public import Aglib.RingTheory.Extension.Presentation.DivideRelation
public import Aglib.RingTheory.Extension.Presentation.RelationMinors
public import Aglib.RingTheory.Extension.Presentation.RelationRowReplacement
public import Aglib.LinearAlgebra.Matrix.MinorIdealResidue
public import Aglib.LinearAlgebra.Matrix.MinorIdealValuation
public import Aglib.RingTheory.MvPolynomial.AffineScaling

/-! # Strict improvement at a rational centre

This file treats the literal translated-origin case. It does not perform the reduction
of a general centre, nor infer smoothness from the unit Fitting ideal without further
geometric hypotheses.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.NeronModification

private theorem minorIdeal_map {R S m n : Type*} [CommRing R] [CommRing S]
    (A : Matrix m n R) (ψ : R →+* S) (r : ℕ) :
    (A.map ψ).minorIdeal r = (A.minorIdeal r).map ψ := by
  rw [Matrix.minorIdeal, Matrix.minorIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨e, c, rfl⟩
    refine ⟨(A.submatrix e c).det, ⟨e, c, rfl⟩, ?_⟩
    simp only [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]
  · rintro ⟨x, ⟨e, c, rfl⟩, rfl⟩
    refine ⟨e, c, ?_⟩
    simp only [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

private theorem residue_eval_affine {R S ι : Type*} [CommRing R] [CommRing S]
    [IsLocalRing S] (ψ : R →+* S) (p : R) (a : ι → R) (z : ι → S)
    (hp : ψ p ∈ IsLocalRing.maximalIdeal S) (f : MvPolynomial ι R) :
    IsLocalRing.residue S (eval₂Hom ψ (fun i => ψ (a i) + ψ p * z i) f) =
      IsLocalRing.residue S (ψ (eval a f)) := by
  have hpzero := (IsLocalRing.residue_eq_zero_iff _).mpr hp
  have he : (IsLocalRing.residue S).comp
      (eval₂Hom ψ (fun i => ψ (a i) + ψ p * z i)) =
      ((IsLocalRing.residue S).comp ψ).comp (eval₂Hom (RingHom.id R) a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp [hpzero]
  exact DFunLike.congr_fun he f

private theorem minorIdeal_le_maximal_of_residue_eq {S m n : Type*} [CommRing S]
    [IsLocalRing S] (A B : Matrix m n S) (r : ℕ)
    (hres : A.map (IsLocalRing.residue S) = B.map (IsLocalRing.residue S))
    (hB : B.minorIdeal r ≤ IsLocalRing.maximalIdeal S) :
    A.minorIdeal r ≤ IsLocalRing.maximalIdeal S := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e, c, rfl⟩
  have hb : (B.submatrix e c).det ∈ IsLocalRing.maximalIdeal S :=
    hB (Ideal.subset_span ⟨e, c, rfl⟩)
  have he := congrArg (fun D => (D.submatrix e c).det) hres
  have hdet : IsLocalRing.residue S (A.submatrix e c).det =
      IsLocalRing.residue S (B.submatrix e c).det := by
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map] using he
  exact (IsLocalRing.residue_eq_zero_iff _).mp
    (hdet.trans ((IsLocalRing.residue_eq_zero_iff _).mpr hb))

variable {R B S ι : Type*} [CommRing R] [CommRing B] [CommRing S]
variable [Algebra R B] [Algebra R S] [IsLocalRing R]
variable [IsDomain S] [IsDiscreteValuationRing S] [Finite ι]

set_option backward.isDefEq.respectTransparency false in
/-- At a literal rational centre, the actual modification strictly enlarges every nonzero
proper evaluated Fitting ideal. The lifted point and its coordinate compatibilities are
constructed, rather than assumed. -/
theorem exists_lift_fittingIdeal_lt (P : Algebra.Generators R B ι) (p : R)
    (a : ι → R) (χ : B →ₐ[R] S) (z : ι → S)
    (hpR : IsLocalRing.maximalIdeal R = Ideal.span {p})
    (hpS : Irreducible (algebraMap R S p))
    (hpoint : ∀ i, χ (P.val i) = algebraMap R S (a i) + algebraMap R S p * z i)
    (k : ℕ)
    (hne : (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom ≠ ⊥)
    (hproper : (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom ≠ ⊤) :
    ∃ χ' : Modification (algebraMap R B p)
        (fun i => P.val i - algebraMap R B (a i)) →ₐ[R] S,
      (∀ b, χ' (of (algebraMap R B p)
        (fun i => P.val i - algebraMap R B (a i)) b) = χ b) ∧
      (∀ i, χ' (coordinate (algebraMap R B p)
        (fun j => P.val j - algebraMap R B (a j)) i) = z i) ∧
      (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom <
        (Module.fittingIdeal _ (KaehlerDifferential R
          (Modification (algebraMap R B p)
            (fun i => P.val i - algebraMap R B (a i)))) k).map χ'.toRingHom := by
  classical
  let := Fintype.ofFinite ι
  let ψ := algebraMap R S
  let g := fun i => P.val i - algebraMap R B (a i)
  let M := Modification (algebraMap R B p) g
  let G := coordinateGenerators P p a
  have hpSmem : ψ p ∈ IsLocalRing.maximalIdeal S := hpS.not_isUnit
  let : IsLocalHom ψ :=
    IsLocalRing.isLocalHom_of_maximalIdeal_eq_span ψ p hpR hpSmem
  have hpSreg : IsRegular (ψ p) := isRegular_iff_ne_zero.mpr hpS.ne_zero
  have hz : ∀ i, χ.toRingHom (algebraMap R B p) * z i = χ.toRingHom (g i) := by
    intro i
    change χ (algebraMap R B p) * z i = χ (P.val i - algebraMap R B (a i))
    rw [map_sub, χ.commutes, χ.commutes, hpoint]
    ring
  have hχp : IsRegular (χ.toRingHom (algebraMap R B p)) := by
    change IsRegular (χ (algebraMap R B p))
    rw [χ.commutes]
    exact hpSreg
  let χ₀ := lift (algebraMap R B p) g χ.toRingHom z hz hχp
  let χ' : M →ₐ[R] S :=
    { χ₀ with
      commutes' := by
        intro r
        rw [IsScalarTower.algebraMap_apply R B M]
        change χ₀ (of (algebraMap R B p) g (algebraMap R B r)) = _
        exact (lift_of _ g χ.toRingHom z hz hχp (algebraMap R B r)).trans (χ.commutes r) }
  have hχof (b : B) : χ' (of (algebraMap R B p) g b) = χ b :=
    lift_of _ g χ.toRingHom z hz hχp b
  have hχz (i : ι) : χ' (coordinate (algebraMap R B p) g i) = z i :=
    lift_coordinate _ g χ.toRingHom z hz hχp i
  refine ⟨χ', hχof, hχz, ?_⟩
  let I := (Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom
  let I' := (Module.fittingIdeal M (KaehlerDifferential R M) k).map χ'.toRingHom
  change I < I'
  let c := Nat.card ι - k
  let Q : Algebra.Presentation R B ι P.ker :=
    { P with
      relation := Subtype.val
      span_range_relation_eq_ker := by
        rw [Subtype.range_coe]
        exact Ideal.span_eq _ }
  let J : Matrix ι P.ker B := fun i f => aeval P.val (pderiv i f.val)
  let A := J.map χ.toRingHom
  have hI : I = A.minorIdeal c := by
    dsimp [I, A, J, c]
    rw [Q.fittingIdeal_kaehler_eq_minorIdeal, ← minorIdeal_map]
    rfl
  obtain ⟨cols, rel, hδ, hspan⟩ :=
    Matrix.exists_minor_span_singleton_eq A c (hI ▸ hne)
  let f : Fin c → MvPolynomial ι R := fun i => (rel i).val
  let δ := (A.submatrix cols rel).det
  let D₀ : Matrix (Fin c) (Fin c) S :=
    fun i j => χ (aeval P.val (pderiv (cols j) (f i)))
  have hD₀ : D₀.det = δ := Matrix.det_transpose _
  have hselected : Ideal.span {δ} = I := hspan.trans hI.symm
  let T : Matrix (Fin c) ι S := fun i j => χ (aeval P.val (pderiv j (f i)))
  have hT : T.minorIdeal c ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨e, d, rfl⟩
    rw [hI]
    apply Ideal.subset_span
    refine ⟨d, rel ∘ e, ?_⟩
    exact Matrix.det_transpose _
  let C₀ : Matrix (Fin c) ι R := fun i j => eval a (pderiv j (f i))
  have hcoords : (fun i => χ (P.val i)) = (fun i => ψ (a i) + ψ p * z i) :=
    funext hpoint
  have heval (q : MvPolynomial ι R) :
      aeval (fun i => ψ (a i) + ψ p * z i) q = χ (aeval P.val q) := by
    rw [comp_aeval_apply, hcoords]
  have hres : (C₀.map ψ).map (IsLocalRing.residue S) =
      T.map (IsLocalRing.residue S) := by
    ext i j
    change IsLocalRing.residue S (ψ (eval a (pderiv j (f i)))) =
      IsLocalRing.residue S (χ (aeval P.val (pderiv j (f i))))
    rw [← heval]
    exact (residue_eval_affine ψ p a z hpSmem (pderiv j (f i))).symm
  have hCtarget : (C₀.map ψ).minorIdeal c ≤ IsLocalRing.maximalIdeal S :=
    minorIdeal_le_maximal_of_residue_eq _ _ _ hres
      (hT.trans (IsLocalRing.le_maximalIdeal hproper))
  have hC : (C₀.map (IsLocalRing.residue R)).minorIdeal c = ⊥ :=
    Matrix.minorIdeal_residue_eq_bot_of_map_le_maximalIdeal C₀ ψ c hCtarget
  obtain ⟨U, F, t, hU, hF, hFker, hrow⟩ :=
    P.exists_relation_rowReplacement f (fun i => (rel i).property) a hC
  have hconst (i : Fin c) : p ∣ eval a (F i) := by
    have hzero : aeval P.val (F i) = 0 := by
      simpa only [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker] using hFker i
    have hsource : ψ (eval a (F i)) ∈ IsLocalRing.maximalIdeal S := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [← residue_eval_affine ψ p a z hpSmem (F i)]
      change IsLocalRing.residue S (aeval (fun i => ψ (a i) + ψ p * z i) (F i)) = 0
      rw [heval, hzero, map_zero, map_zero]
    apply Ideal.mem_span_singleton.mp
    rw [← hpR, ← IsLocalRing.maximalIdeal_comap ψ]
    exact hsource
  choose cs hcs using hconst
  choose H Qs hQs hHs hdivs hHker using
    fun i => exists_divided_relation P p a (F i) (hFker i) (cs i) (hcs i)
  have hpM : IsRegular (algebraMap R M p) := by
    have hm := isRegular_of (algebraMap R B p) g
    change IsRegular (algebraMap B M (algebraMap R B p)) at hm
    rwa [← IsScalarTower.algebraMap_apply R B M p] at hm
  obtain ⟨h₂, hh₂, hh₂ker⟩ := G.exists_divided_relation_of_local_point χ' p (cs t)
    (fun j => eval a (pderiv j (F t))) (H t) (Qs t) (hHker t) hpR
    (fun j => Ideal.mem_span_singleton.mp (hpR ▸ hrow j)) (hHs t) hpM
  let H' := Function.update H t h₂
  have hH'ker (i : Fin c) : H' i ∈ G.ker := by
    by_cases hi : i = t
    · subst i
      simpa only [H', Function.update_self] using hh₂ker
    · simpa only [H', Function.update_of_ne hi] using hHker i
  let D : Matrix (Fin c) (Fin c) S := fun i j => aeval z (pderiv (cols j) (H i))
  let N : Matrix (Fin c) (Fin c) S := fun i j => aeval z (pderiv (cols j) (H' i))
  have hJac : D = U.map ψ * D₀ := by
    ext i j
    change aeval z (pderiv (cols j) (H i)) = _
    rw [aeval_pderiv_of_affine_scaling_eq (F i) (H i) a p (hdivs i) z hpSreg, heval]
    rw [hF i]
    simp only [map_sum, pderiv_C_mul, map_mul, aeval_C, AlgHom.commutes,
      Matrix.mul_apply, Matrix.map_apply, D₀, ψ]
  have hrowScale : D = N.updateRow t (ψ p • N t) := by
    ext i j
    by_cases hi : i = t
    · subst i
      simp only [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul]
      change aeval z (pderiv (cols j) (H t)) = ψ p * aeval z (pderiv (cols j) (H' t))
      rw [hh₂]
      simp only [pderiv_C_mul, map_mul, aeval_C, H', Function.update_self, ψ]
    · simp only [Matrix.updateRow_ne hi]
      change aeval z (pderiv (cols j) (H i)) = aeval z (pderiv (cols j) (H' i))
      simp only [H', Function.update_of_ne hi]
  have hdet : ψ U.det * δ = ψ p * N.det := by
    calc
      ψ U.det * δ = (U.map ψ).det * D₀.det := by
        rw [hD₀, RingHom.map_det, RingHom.mapMatrix_apply]
      _ = (U.map ψ * D₀).det := (Matrix.det_mul _ _).symm
      _ = D.det := congrArg Matrix.det hJac.symm
      _ = ψ p * N.det := by
        rw [hrowScale, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  have hu : IsUnit (ψ U.det) :=
    ((Matrix.isUnit_iff_isUnit_det U).mp hU).map ψ
  have hNne : N.det ≠ 0 := by
    intro hn
    rw [hn, mul_zero] at hdet
    exact hδ ((mul_eq_zero.mp hdet).resolve_left hu.ne_zero)
  have hNmem : N.det ∈ I' := by
    have hm := Ideal.mem_map_of_mem χ'.toRingHom
      (G.det_relation_pderiv_mem_fittingIdeal k H' hH'ker cols)
    change χ'.toRingHom
      (Matrix.of fun j i => aeval G.val (pderiv (cols i) (H' j))).det ∈ I' at hm
    have hmap := χ'.toRingHom.map_det
      (Matrix.of fun j i => aeval G.val (pderiv (cols i) (H' j)))
    have hm' := hmap ▸ hm
    have hv (i : ι) : χ' (G.val i) = z i := hχz i
    have he : χ'.toRingHom.mapMatrix
        (Matrix.of fun j i => aeval G.val (pderiv (cols i) (H' j))) = N := by
      ext i j
      change χ' (aeval G.val (pderiv (cols j) (H' i))) =
        aeval z (pderiv (cols j) (H' i))
      exact (comp_aeval_apply G.val χ' (pderiv (cols j) (H' i))).trans
        (congrArg (fun v => aeval v (pderiv (cols j) (H' i))) (funext hv))
    rwa [he] at hm'
  rw [← hselected, ← Ideal.span_singleton_mul_left_unit hu δ, hdet]
  apply lt_of_lt_of_le (Ideal.span_singleton_lt_span_singleton.mpr ?_)
    ((Ideal.span_singleton_le_iff_mem I').mpr hNmem)
  exact ⟨hNne, ψ p, hpS.not_isUnit, mul_comm _ _⟩

end Algebra.NeronModification
