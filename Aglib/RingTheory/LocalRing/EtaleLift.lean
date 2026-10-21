/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Finite etale lifts of separable residue extensions

A monic polynomial whose reduction is separable defines a finite etale algebra
over a local ring. Lifting a primitive element's minimal polynomial therefore
lifts every finite separable extension of the actual residue field. Finite
products then lift every etale residue algebra. The fibre comparison is an
algebra equivalence from the canonical tensor product.

This construction needs neither a Henselian, Noetherian nor excellent base.
It supplies residue essential surjectivity, without asserting full faithfulness
or any proper-scheme comparison.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped TensorProduct

universe u v

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Coprimality of a monic polynomial and another polynomial is detected in
the residue field. -/
theorem isCoprime_of_monic_of_residue {f g : R[X]} (hf : f.Monic)
    (h : IsCoprime (f.map (residue R)) (g.map (residue R))) : IsCoprime f g := by
  apply (isUnit_resultant_iff_isCoprime hf).mp
  apply (residue_ne_zero_iff_isUnit _).mp
  have hdeg : (g.map (residue R)).natDegree ≤ g.natDegree := natDegree_map_le
  have hr : residue R (resultant f g) =
      resultant (f.map (residue R)) (g.map (residue R)) := by
    rw [← resultant_map_map, ← hf.natDegree_map (residue R)]
    have he := resultant_add_right_deg (f.map (residue R)) (g.map (residue R))
      (f.map (residue R)).natDegree (g.map (residue R)).natDegree
      (g.natDegree - (g.map (residue R)).natDegree) le_rfl
    simpa only [Nat.add_sub_of_le hdeg, (hf.map (residue R)).coeff_natDegree,
      one_pow, one_mul] using he
  rw [hr]
  exact isUnit_iff_ne_zero.mp ((isUnit_resultant_iff_isCoprime (hf.map _)).mpr h)

/-- A monic polynomial over a local ring is separable when its residue
polynomial is separable. -/
theorem separable_of_monic_of_residue {f : R[X]} (hf : f.Monic)
    (h : (f.map (residue R)).Separable) : f.Separable := by
  apply isCoprime_of_monic_of_residue hf
  simpa only [separable_def, ← derivative_map] using h

end IsLocalRing

namespace AdjoinRoot

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- A monic separable polynomial defines an etale root algebra. -/
theorem etale_of_monic_of_separable {f : R[X]} (hf : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := hs
  let P : StandardEtalePair R :=
    { f := f
      monic_f := hf
      g := 1
      cond := ⟨b, a, 0, by simpa only [pow_zero, mul_comm, add_comm] using hab⟩ }
  let e : P.Ring ≃ₐ[R] AdjoinRoot f :=
    AlgEquiv.ofAlgHom
      (P.lift (root f) ⟨by change aeval (root f) f = 0; simp [aeval_eq], by simp [P]⟩)
      (liftAlgHom f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1)
      (by ext; simp only [AlgHom.comp_apply, liftAlgHom_root,
        StandardEtalePair.lift_X, AlgHom.id_apply])
      (by apply P.hom_ext; simp only [AlgHom.comp_apply, StandardEtalePair.lift_X,
        liftAlgHom_root, AlgHom.id_apply])
  exact Algebra.Etale.of_equiv e

/-- Base change of a root algebra along the actual scalar map, with a specified
mapped polynomial. -/
def baseChangeEquiv {S : Type v} [CommRing S] [Algebra R S]
    (f : R[X]) (g : S[X]) (h : f.map (algebraMap R S) = g) :
    S ⊗[R] AdjoinRoot f ≃ₐ[S] AdjoinRoot g :=
  (tensorAlgEquiv f
    (f.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom) rfl).trans
    (mapAlgEquiv (Algebra.TensorProduct.rid R S S) _ g (by
      apply Associated.of_eq
      rw [Polynomial.map_map]
      convert h using 1
      congr 1
      ext x
      simp [Algebra.TensorProduct.rid_tmul, Algebra.smul_def]))

@[simp]
theorem baseChangeEquiv_root {S : Type v} [CommRing S] [Algebra R S]
    (f : R[X]) (g : S[X]) (h : f.map (algebraMap R S) = g) :
    baseChangeEquiv f g h (1 ⊗ₜ[R] root f) = root g := by
  simp only [baseChangeEquiv, AlgEquiv.trans_apply, tensorAlgEquiv_root,
    coe_mapAlgEquiv, map_root]

end AdjoinRoot

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (L : Type v) [Field L] [Algebra (ResidueField R) L]
  [FiniteDimensional (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L]

/-- Every finite separable residue field extension is the literal residue fibre
of a monic separable root algebra over the local ring. -/
theorem exists_monic_separable_residue_lift :
    ∃ f : R[X], f.Monic ∧ f.Separable ∧
      Nonempty (ResidueField R ⊗[R] AdjoinRoot f ≃ₐ[ResidueField R] L) := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField R) L
  let q := minpoly (ResidueField R) pb.gen
  have hq : q.Monic := minpoly.monic pb.isIntegral_gen
  obtain ⟨f, hfq, _, hfm⟩ := lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := R)) q) hq
  have hfs : f.Separable := separable_of_monic_of_residue hfm (by
    rw [hfq]
    exact Algebra.IsSeparable.isSeparable (ResidueField R) pb.gen)
  refine ⟨f, hfm, hfs, ⟨?_⟩⟩
  exact (AdjoinRoot.baseChangeEquiv f q hfq).trans
    (AdjoinRoot.equiv' q pb (by simp [q, AdjoinRoot.aeval_eq]) (minpoly.aeval _ _))

/-- A finite separable extension of the residue field of any local ring lifts
to an actual finite etale algebra, with its canonical residue tensor product.
The algebra has the universe of the base; the extension may have an independent
universe. -/
theorem exists_finite_etale_residue_lift :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧
        Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  obtain ⟨f, hfm, hfs, e⟩ := exists_monic_separable_residue_lift R L
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, hfm.finite_adjoinRoot,
    AdjoinRoot.etale_of_monic_of_separable hfm hfs, e⟩

variable {L}

/-- Every etale algebra over the residue field of a local ring is the actual
residue fibre of a finite etale algebra. The field decomposition and all scalar
extensions are algebra equivalences for the given residue algebra structure. -/
theorem exists_finite_etale_residue_lift_of_etale
    (B : Type v) [CommRing B] [Algebra (ResidueField R) B]
    [Algebra.Etale (ResidueField R) B] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧
        Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] B) := by
  classical
  obtain ⟨ι, hι, K, hK, hAlg, e, h⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (ResidueField R) B).mp inferInstance
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : ∀ i, Field (K i) := hK
  let : ∀ i, Algebra (ResidueField R) (K i) := hAlg
  let : ∀ i, Module.Finite (ResidueField R) (K i) := fun i ↦ (h i).1
  let : ∀ i, Algebra.IsSeparable (ResidueField R) (K i) := fun i ↦ (h i).2
  choose f hm hs he using fun i ↦ exists_monic_separable_residue_lift R (K i)
  let : ∀ i, Module.Finite R (AdjoinRoot (f i)) := fun i ↦ (hm i).finite_adjoinRoot
  let : ∀ i, Algebra.Etale R (AdjoinRoot (f i)) := fun i ↦
    AdjoinRoot.etale_of_monic_of_separable (hm i) (hs i)
  refine ⟨∀ i, AdjoinRoot (f i), inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨?_⟩⟩
  exact ((Algebra.TensorProduct.piRight R (ResidueField R) (ResidueField R)
    (fun i ↦ AdjoinRoot (f i))).trans
      (AlgEquiv.piCongrRight fun i ↦ (he i).some)).trans e.symm

end IsLocalRing
