/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.RationalPointEtaleLocal
public import Aglib.RingTheory.LocalRing.EtaleLift
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.PrimitiveElement

/-! # Finitely presented etale neighborhoods of separable residue points

Finite coefficient families are lifted over one original principal open.
A single standard-etale root algebra retains the primitive residue element;
the actual standard-etale tensor slice supplies the original smooth-algebra
map. No localization at the final residue prime replaces this etale algebra.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing
open scoped TensorProduct

universe u v

namespace Algebra.Smooth.SeparableResiduePoint

variable (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]

/-- One original denominator lifts any finite family of residue coefficients. -/
theorem exists_principal_residue_lifts {ι : Type v} [Finite ι]
    (v : ι → p.ResidueField) :
    ∃ (a : R) (_ : a ∉ p) (ρ : Localization.Away a →ₐ[R] p.ResidueField)
      (w : ι → Localization.Away a), ∀ i, ρ (w i) = v i := by
  choose x hx using fun i => residue_surjective (R := Localization.AtPrime p) (v i)
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl x
  choose b hb using ha
  have hu : IsUnit (algebraMap R p.ResidueField a.1) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hm : a.1 ∈ RingHom.ker (algebraMap R p.ResidueField) := h
    rw [p.ker_algebraMap_residueField] at hm
    exact a.2 hm
  let ρ : Localization.Away a.1 →ₐ[R] p.ResidueField :=
    IsLocalization.Away.liftAlgHom (f := Algebra.ofId R p.ResidueField) a.1 hu
  let w (i : ι) : Localization.Away a.1 :=
    IsLocalization.mk' _ (b i) (⟨a.1, Submonoid.mem_powers _⟩ : Submonoid.powers a.1)
  refine ⟨a.1, a.2, ρ, w, fun i => ?_⟩
  apply mul_right_cancel₀ (isUnit_iff_ne_zero.mp hu)
  have hw := congrArg ρ (IsLocalization.mk'_spec (Localization.Away a.1) (b i)
    (⟨a.1, Submonoid.mem_powers _⟩ : Submonoid.powers a.1))
  have hbi := congrArg (residue (Localization.AtPrime p)) (hb i)
  have hbi' : algebraMap R p.ResidueField (b i) =
      algebraMap R p.ResidueField a.1 * residue (Localization.AtPrime p) (x i) := by
    simpa only [Algebra.smul_def, map_mul, ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply] using hbi
  have hw' : ρ (w i) * algebraMap R p.ResidueField a.1 =
      algebraMap R p.ResidueField (b i) := by
    simpa only [map_mul, ρ.commutes] using hw
  simpa only [hx i, mul_comm] using hw'.trans hbi'

/-- All coefficients of finitely many original polynomials lift together. -/
theorem exists_principal_polynomial_lifts {ι : Type v} [Finite ι]
    (f : ι → p.ResidueField[X]) :
    ∃ (a : R) (_ : a ∉ p) (ρ : Localization.Away a →ₐ[R] p.ResidueField),
      ∀ i, f i ∈ Polynomial.lifts ρ.toRingHom := by
  classical
  let := Fintype.ofFinite ι
  let s : Finset p.ResidueField := Finset.univ.biUnion fun i => (f i).coeffs
  obtain ⟨a, ha, ρ, w, hw⟩ := exists_principal_residue_lifts R p (fun z : s => z.1)
  refine ⟨a, ha, ρ, fun i => (Polynomial.lifts_iff_coeffs_subset_range (f i)).mpr ?_⟩
  intro c hc
  have hcs : c ∈ s := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩
  exact ⟨w ⟨c, hcs⟩, hw ⟨c, hcs⟩⟩

variable (L : Type u) [Field L] [Algebra p.ResidueField L] [Algebra R L]
  [IsScalarTower R p.ResidueField L]
  [FiniteDimensional p.ResidueField L] [Algebra.IsSeparable p.ResidueField L]

/-- One genuine etale algebra contains lifts of a prescribed finite family
and of the original primitive residue element. -/
theorem exists_etale_residue_lifts {ι : Type v} [Finite ι] (y : ι → L) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Algebra.Etale R E ∧ ∃ (l : E →ₐ[R] L) (z : ι → E)
        (pb : PowerBasis p.ResidueField L) (t : E),
        (∀ i, l (z i) = y i) ∧ l t = pb.gen := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable p.ResidueField L
  choose g hg using fun i => pb.exists_eq_aeval' (y i)
  let f : Option ι → p.ResidueField[X]
    | none => minpoly p.ResidueField pb.gen
    | some i => g i
  obtain ⟨a, ha, ρ, hf⟩ := exists_principal_polynomial_lifts R p f
  let A := Localization.Away a
  obtain ⟨F, hF, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (hf none) (minpoly.monic pb.isIntegral_gen)
  choose G hG using fun i => (Polynomial.mem_lifts (g i)).mp (hf (some i))
  let P : StandardEtalePair A := ⟨F, hmonic, F.derivative, 1, 0, 1, by simp⟩
  let : Algebra A L := ((algebraMap p.ResidueField L).comp ρ.toRingHom).toAlgebra
  let : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R L r = algebraMap p.ResidueField L (ρ (algebraMap R A r))
    rw [ρ.commutes, IsScalarTower.algebraMap_apply R p.ResidueField L]
  have heval (q : A[X]) : aeval pb.gen q =
      aeval pb.gen (q.map ρ.toRingHom) := by
    simp only [aeval_def, eval₂_map, RingHom.algebraMap_toAlgebra]
  have hroot : aeval pb.gen F = 0 := by
    rw [heval, hF]
    exact minpoly.aeval p.ResidueField pb.gen
  have hderiv : IsUnit (aeval pb.gen F.derivative) := by
    rw [heval, ← derivative_map, hF]
    exact isUnit_iff_ne_zero.mpr
      ((Algebra.IsSeparable.isSeparable p.ResidueField pb.gen).aeval_derivative_ne_zero
        (minpoly.aeval p.ResidueField pb.gen))
  let E := P.Ring
  let lA : E →ₐ[A] L := P.lift pb.gen ⟨hroot, hderiv⟩
  let : Algebra R E := ((algebraMap A E).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.Etale R E := Algebra.Etale.comp R A E
  refine ⟨E, inferInstance, inferInstance, inferInstance, lA.restrictScalars R,
    fun i => aeval P.X (G i), pb, P.X, ?_, P.lift_X pb.gen ⟨hroot, hderiv⟩⟩
  intro i
  change lA (aeval P.X (G i)) = y i
  have hlX : lA P.X = pb.gen := P.lift_X pb.gen ⟨hroot, hderiv⟩
  rw [← aeval_algHom_apply, hlX, heval, hG i]
  exact (hg i).symm

/-- The primitive element already in the image identifies the residue field
at the exact kernel of the original point. No global surjectivity is assumed. -/
def residueEquivOfPowerBasis {E : Type u} [CommRing E] [Algebra R E]
    (l : E →ₐ[R] L) (pb : PowerBasis p.ResidueField L) (t : E) (ht : l t = pb.gen) :
    let q := RingHom.ker l.toRingHom
    letI : q.IsPrime := RingHom.ker_isPrime _
    q.ResidueField ≃+* L := by
  let q := RingHom.ker l.toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime _
  let η : q.ResidueField →+* L := Ideal.ResidueField.lift q l.toRingHom le_rfl
    (fun a ha => isUnit_iff_ne_zero.mpr ha)
  have hqp : p = q.comap (algebraMap R E) := by
    ext r
    change r ∈ p ↔ l (algebraMap R E r) = 0
    rw [l.commutes, IsScalarTower.algebraMap_apply R p.ResidueField L,
      map_eq_zero_iff (algebraMap p.ResidueField L) (algebraMap p.ResidueField L).injective]
    exact (Ideal.algebraMap_residueField_eq_zero (I := p)).symm
  have hη (z : E) : η (algebraMap E q.ResidueField z) = l z :=
    Ideal.ResidueField.lift_algebraMap _ _ _ _ z
  let v := Ideal.ResidueField.map p q (algebraMap R E) hqp
  have hv : η.comp v = algebraMap p.ResidueField L := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    change η (v (algebraMap R p.ResidueField r)) =
      algebraMap p.ResidueField L (algebraMap R p.ResidueField r)
    rw [show v (algebraMap R p.ResidueField r) =
      algebraMap E q.ResidueField (algebraMap R E r) from
        Ideal.ResidueField.map_algebraMap p q _ hqp r, hη, l.commutes]
    exact IsScalarTower.algebraMap_apply R p.ResidueField L r
  let : Algebra p.ResidueField q.ResidueField := v.toAlgebra
  let ηa : q.ResidueField →ₐ[p.ResidueField] L :=
    { __ := η, commutes' := fun x => DFunLike.congr_fun hv x }
  refine RingEquiv.ofBijective η ⟨η.injective, fun x => ?_⟩
  obtain ⟨g, hg⟩ := pb.exists_eq_aeval' x
  refine ⟨aeval (algebraMap E q.ResidueField t) g, ?_⟩
  change ηa (aeval (algebraMap E q.ResidueField t) g) = x
  rw [← aeval_algHom_apply]
  change aeval (η (algebraMap E q.ResidueField t)) g = x
  rw [hη, ht]
  exact hg.symm

include p in
/-- A finite separable residue point of the original smooth algebra extends
to a section over a genuinely etale, hence finitely presented, base algebra. -/
theorem exists_etale_lift (B : Type u) [CommRing B] [Algebra R B]
    [Algebra.Smooth R B] (ψ : B →ₐ[R] L) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Algebra.Etale R E ∧ ∃ (ε : B →ₐ[R] E) (l : E →ₐ[R] L), l.comp ε = ψ ∧
        let q := RingHom.ker l.toRingHom
        letI : q.IsPrime := RingHom.ker_isPrime _
        ∃ e : q.ResidueField ≃+* L, ∀ z : E, e (algebraMap E q.ResidueField z) = l z := by
  let q := RingHom.ker ψ.toRingHom
  let : q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨r, hr, n, hP, htower, hstd⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := q)
  let P := MvPolynomial (Fin n) R
  let B' := Localization.Away r
  let : Algebra P B' := hP
  let : IsScalarTower R P B' := htower
  let : Algebra.IsStandardEtale P B' := hstd
  let ψ' : B' →ₐ[R] L := IsLocalization.Away.liftAlgHom r
    (isUnit_iff_ne_zero.mpr hr)
  obtain ⟨A, hA, aRA, hEtale, lA, z, pb, t, hz, ht⟩ :=
    exists_etale_residue_lifts R p L (fun i : Fin n => ψ' (algebraMap P B' (MvPolynomial.X i)))
  let := hA
  let := aRA
  let := hEtale
  let ρ : P →ₐ[R] A := MvPolynomial.aeval z
  let : Algebra P A := ρ.toRingHom.toAlgebra
  let : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' ρ.comp_algebraMap.symm
  let : Algebra A L := lA.toRingHom.toAlgebra
  let : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun r => (lA.commutes r).symm
  let : Algebra P L := ((lA.toRingHom).comp ρ.toRingHom).toAlgebra
  let : IsScalarTower P A L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ'.comp (IsScalarTower.toAlgHom R P B') = lA.comp ρ := by
    ext i
    change ψ' (algebraMap P B' (MvPolynomial.X i)) = lA (MvPolynomial.aeval z (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
    exact (hz i).symm
  let ψP : B' →ₐ[P] L := { __ := ψ'.toRingHom, commutes' := fun x => DFunLike.congr_fun hcomp x }
  let E := A ⊗[P] B'
  let : IsScalarTower R A E := inferInstance
  let : Algebra.Etale R E := Algebra.Etale.comp R A E
  let lP : E →ₐ[P] L := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom P A L) ψP (fun _ _ => .all _ _)
  have hlP (a : A) (b : B') : lP (a ⊗ₜ[P] b) = lA a * ψ' b :=
    Algebra.TensorProduct.lift_tmul (IsScalarTower.toAlgHom P A L) ψP
      (fun _ _ => .all _ _) a b
  let l : E →ₐ[R] L := {
    __ := lP.toRingHom
    commutes' := fun r => by
      change lP ((algebraMap R A r) ⊗ₜ[P] (1 : B')) = algebraMap R L r
      rw [hlP, map_one, mul_one, lA.commutes] }
  let ε : B →ₐ[R] E :=
    ((Algebra.TensorProduct.includeRight : B' →ₐ[P] E).restrictScalars R).comp
      (IsScalarTower.toAlgHom R B B')
  have hε : l.comp ε = ψ := by
    ext b
    change lP (1 ⊗ₜ[P] (algebraMap B B' b)) = ψ b
    rw [hlP, map_one, one_mul]
    exact IsLocalization.Away.lift_eq r (isUnit_iff_ne_zero.mpr hr) b
  have htl : l (t ⊗ₜ[P] (1 : B')) = pb.gen := by
    change lP (t ⊗ₜ[P] (1 : B')) = pb.gen
    rw [hlP, map_one, mul_one]
    exact ht
  refine ⟨E, inferInstance, inferInstance, inferInstance, ε, l, hε,
    residueEquivOfPowerBasis R p L l pb (t ⊗ₜ[P] (1 : B')) htl, ?_⟩
  intro z
  let : (RingHom.ker l.toRingHom).IsPrime := RingHom.ker_isPrime _
  exact Ideal.ResidueField.lift_algebraMap (RingHom.ker l.toRingHom) l.toRingHom
    le_rfl (fun a ha => isUnit_iff_ne_zero.mpr ha) z

end Algebra.Smooth.SeparableResiduePoint
