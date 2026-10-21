/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationLocalRing
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Henselian

/-!
# Henselianity of the constructed henselization

Finite coefficient tuples descend to a common etale neighborhood. Native
polynomial lifting then preserves monicity. The standard etale algebra of a
monic polynomial localized at its derivative supplies an actual simple root
in the filtered colimit. Thus henselianity is proved, not assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Polynomial IsLocalRing

namespace Henselization

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- A finite tuple of colimit elements is represented in one actual stage. -/
lemma exists_fin_rep {n : ℕ} (x : Fin n → Henselization R) :
    ∃ (S : PointedEtaleNeighborhood R) (a : Fin n → S.algebra),
      ∀ i, ι R S (a i) = x i := by
  induction n with
  | zero =>
    let S : PointedEtaleNeighborhood R := Classical.choice inferInstance
    exact ⟨S, Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨S, a, ha⟩ := ih (fun i => x i.succ)
    obtain ⟨T, f, b, hb⟩ := exists_rep_over R (x 0) S
    refine ⟨T, Fin.cases b (fun i => f.val (a i)), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hb
    · exact (AlgHom.congr_fun (ι_naturality f) (a j)).trans (ha j)

/-- Every monic polynomial descends to a monic polynomial in a single native
pointed etale stage. The maps are literal coefficient maps. -/
lemma exists_monic_polynomial_rep (f : (Henselization R)[X]) (hf : f.Monic) :
    ∃ (S : PointedEtaleNeighborhood R) (q : S.algebra[X]),
      q.map (ι R S).toRingHom = f ∧ q.Monic := by
  obtain ⟨S, a, ha⟩ := exists_fin_rep R
    (fun i : Fin (f.natDegree + 1) => f.coeff i)
  have hlift : f ∈ Polynomial.lifts (ι R S).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    by_cases hi : i < f.natDegree + 1
    · exact ⟨a ⟨i, hi⟩, ha ⟨i, hi⟩⟩
    · have hzero : f.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      exact ⟨0, by rw [map_zero, hzero]⟩
  obtain ⟨q, hq, _, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hf
  exact ⟨S, q, hq, hqm⟩

/-- A simple root in the original residue field lifts through an actual
standard etale neighborhood to the constructed henselization. -/
lemma exists_root_of_monic_residue (f : (Henselization R)[X]) (hf : f.Monic)
    (b : ResidueField R) (hb : (f.map (residue R).toRingHom).IsRoot b)
    (hdb : (f.derivative.map (residue R).toRingHom).eval b ≠ 0) :
    ∃ a : Henselization R, f.IsRoot a ∧ residue R a = b := by
  obtain ⟨S, q, hq, hqm⟩ := exists_monic_polynomial_rep R f hf
  have hres : q.map S.point.toRingHom = f.map (residue R).toRingHom := by
    rw [← hq, Polynomial.map_map]
    rw [show (residue R).toRingHom.comp (ι R S).toRingHom = S.point.toRingHom from
      congrArg AlgHom.toRingHom (residue_comp_ι R S)]
  have hresd : q.derivative.map S.point.toRingHom =
      f.derivative.map (residue R).toRingHom := by
    rw [← Polynomial.derivative_map, hres, Polynomial.derivative_map]
  let P : StandardEtalePair S.algebra :=
    { f := q
      monic_f := hqm
      g := q.derivative
      cond := ⟨1, 0, 1, by simp⟩ }
  let : Algebra S.algebra (ResidueField R) := S.point.toRingHom.toAlgebra
  let : IsScalarTower R S.algebra (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq fun r => (S.point.commutes r).symm
  have hP : P.HasMap b := by
    constructor
    · change q.eval₂ S.point.toRingHom b = 0
      rw [← Polynomial.eval_map, hres]
      exact hb
    · change IsUnit (q.derivative.eval₂ S.point.toRingHom b)
      apply isUnit_iff_ne_zero.mpr
      rw [← Polynomial.eval_map, hresd]
      exact hdb
  let : Algebra R P.Ring := Algebra.compHom P.Ring (algebraMap R S.algebra)
  let : IsScalarTower R S.algebra P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale R P.Ring := Algebra.Etale.comp R S.algebra P.Ring
  let p : P.Ring →ₐ[R] ResidueField R := (P.lift b hP).restrictScalars R
  obtain ⟨T, e, he⟩ := PointedEtaleNeighborhood.exists_equiv P.Ring p
  let j : S ⟶ T :=
    ⟨e.toAlgHom.comp (IsScalarTower.toAlgHom R S.algebra P.Ring), by
      rw [← AlgHom.comp_assoc, he]
      apply AlgHom.ext
      intro c
      exact (P.lift b hP).commutes c⟩
  let tR : P.Ring →ₐ[R] Henselization R := (ι R T).comp e.toAlgHom
  have ht : tR.toRingHom.comp (algebraMap S.algebra P.Ring) = (ι R S).toRingHom := by
    exact congrArg AlgHom.toRingHom (ι_naturality j)
  let : Algebra S.algebra (Henselization R) := (ι R S).toRingHom.toAlgebra
  let t : P.Ring →ₐ[S.algebra] Henselization R :=
    { tR.toRingHom with commutes' c := RingHom.congr_fun ht c }
  refine ⟨t P.X, ?_, ?_⟩
  · change f.eval (t P.X) = 0
    rw [← hq, Polynomial.eval_map]
    change aeval (t P.X) q = 0
    rw [Polynomial.aeval_algHom_apply]
    have h := congrArg t P.hasMap_X.1
    simpa only [map_zero] using h
  · change residue R (ι R T (e P.X)) = b
    calc
      residue R (ι R T (e P.X)) = T.point (e P.X) :=
        AlgHom.congr_fun (residue_comp_ι R T) (e P.X)
      _ = P.lift b hP P.X := AlgHom.congr_fun he P.X
      _ = b := P.lift_X b hP

instance : HenselianLocalRing (Henselization R) where
  is_henselian f hf a₀ ha₀ hda₀ := by
    have hb : (f.map (residue R).toRingHom).IsRoot (residue R a₀) := by
      change (f.map (residue R).toRingHom).eval ((residue R).toRingHom a₀) = 0
      rw [Polynomial.eval_map_apply]
      rw [maximalIdeal_eq_ker_residue] at ha₀
      exact ha₀
    have hdb : (f.derivative.map (residue R).toRingHom).eval (residue R a₀) ≠ 0 := by
      change (f.derivative.map (residue R).toRingHom).eval ((residue R).toRingHom a₀) ≠ 0
      rw [Polynomial.eval_map_apply]
      exact isUnit_iff_ne_zero.mp (hda₀.map (residue R).toRingHom)
    obtain ⟨a, ha, har⟩ := exists_root_of_monic_residue R f hf (residue R a₀) hb hdb
    refine ⟨a, ha, ?_⟩
    rw [maximalIdeal_eq_ker_residue]
    change residue R (a - a₀) = 0
    rw [map_sub, har, sub_self]

end Henselization
