/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationTriangular
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFormal
public import Aglib.RingTheory.Henselian.PolynomialLocalTriangularFormal

/-!
# Formal compatibility of actual henselization triangular coordinates

The forward square follows from the proved local universal property and the
literal original local-ring square. Genuine inverse laws give the inverse
square used to transport normalized solutions back to the original source.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace PolynomialLocalHenselization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
variable (p : Fin n) (e : Fin n → ℕ) (he : ∀ i, i ≠ p → 0 < e i)

/-- The original formal map intertwines the actual source and formal coordinate automorphisms. -/
theorem toFormalSeries_comp_triangularAlgEquiv :
    (toFormalSeries R n).comp (triangularAlgEquiv R n p e he).toAlgHom =
      ((MvPowerSeries.triangularAlgEquiv
        (R := AdicCompletion (maximalIdeal R) R) p e he).restrictScalars R).toAlgHom.comp
          (toFormalSeries R n) := by
  let A := PolynomialLocalRing R n
  let B := PolynomialLocalRing.FormalSeries R n
  let a := PolynomialLocalRing.triangularAlgEquiv R n p e he
  let b := MvPowerSeries.triangularAlgEquiv (R := AdicCompletion (maximalIdeal R) R) p e he
  let α := triangularAlgEquiv R n p e he
  let φ : A →ₐ[R] B := (PolynomialLocalRing.toFormalSeries R n).comp a.toAlgHom
  let f : PolynomialLocalHenselization R n →ₐ[R] B := (toFormalSeries R n).comp α.toAlgHom
  let g : PolynomialLocalHenselization R n →ₐ[R] B :=
    (b.restrictScalars R).toAlgHom.comp (toFormalSeries R n)
  let : HenselianLocalRing B := PolynomialLocalRing.formalSeries_henselian R n
  let : IsLocalHom a.toRingHom := IsLocalHom.of_surjective _ a.surjective
  let : IsLocalHom α.toRingHom := IsLocalHom.of_surjective _ α.surjective
  let : IsLocalHom b.toRingHom := IsLocalHom.of_surjective _ b.surjective
  let : IsLocalHom φ.toRingHom := by
    change IsLocalHom ((PolynomialLocalRing.toFormalSeries R n).toRingHom.comp a.toRingHom)
    infer_instance
  have hf : f.comp (IsScalarTower.toAlgHom R A (PolynomialLocalHenselization R n)) = φ := by
    apply AlgHom.ext
    intro x
    change toFormalSeries R n (triangularAlgEquiv R n p e he
      (algebraMap A (PolynomialLocalHenselization R n) x)) =
        PolynomialLocalRing.toFormalSeries R n (a x)
    rw [triangularAlgEquiv_algebraMap]
    exact AlgHom.congr_fun (toFormalSeries_comp_of R n) (a x)
  have hg : g.comp (IsScalarTower.toAlgHom R A (PolynomialLocalHenselization R n)) = φ := by
    apply AlgHom.ext
    intro x
    change b (toFormalSeries R n (algebraMap A (PolynomialLocalHenselization R n) x)) =
      PolynomialLocalRing.toFormalSeries R n (a x)
    rw [show toFormalSeries R n (algebraMap A (PolynomialLocalHenselization R n) x) =
      PolynomialLocalRing.toFormalSeries R n x from
        AlgHom.congr_fun (toFormalSeries_comp_of R n) x]
    exact (AlgHom.congr_fun
      (PolynomialLocalRing.toFormalSeries_comp_triangularAlgEquiv R n p e he) x).symm
  have hflocal : IsLocalHom f.toRingHom := by
    change IsLocalHom ((toFormalSeries R n).toRingHom.comp α.toRingHom)
    infer_instance
  have hglocal : IsLocalHom g.toRingHom := by
    change IsLocalHom (b.toRingHom.comp (toFormalSeries R n).toRingHom)
    infer_instance
  have h := existsUnique_local_extension R n B φ
  exact (h.choose_spec.2 f ⟨hflocal, hf⟩).trans (h.choose_spec.2 g ⟨hglocal, hg⟩).symm

/-- The actual inverse source change maps to the inverse formal triangular change. -/
theorem toFormalSeries_triangularAlgEquiv_symm (x : PolynomialLocalHenselization R n) :
    toFormalSeries R n ((triangularAlgEquiv R n p e he).symm x) =
      (MvPowerSeries.triangularAlgEquiv
        (R := AdicCompletion (maximalIdeal R) R) p e he).symm (toFormalSeries R n x) := by
  let a := triangularAlgEquiv R n p e he
  let b := MvPowerSeries.triangularAlgEquiv
    (R := AdicCompletion (maximalIdeal R) R) p e he
  apply b.injective
  have h := AlgHom.congr_fun (toFormalSeries_comp_triangularAlgEquiv R n p e he) (a.symm x)
  change toFormalSeries R n (a (a.symm x)) = b (toFormalSeries R n (a.symm x)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  change b (toFormalSeries R n (a.symm x)) = b (b.symm (toFormalSeries R n x))
  rw [AlgEquiv.apply_symm_apply]
  exact h.symm

end PolynomialLocalHenselization
