/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Finite fixed vectors of a Frobenius-semilinear map

A prime-field-independent family of Frobenius-fixed vectors is independent over
the ambient characteristic-`p` field. Consequently the fixed submodule of a
Frobenius-semilinear endomorphism of a finite-dimensional vector space has
prime-field dimension at most the ambient dimension and has finite cardinality.
Neither perfectness of the field nor invertibility of the operator is required.
The current consumer is proper Artin--Schreier cohomology finiteness.
-/

@[expose] public noncomputable section

namespace LinearMap

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  (F : V →ₛₗ[_root_.frobenius k p] V)

section PrimeScalars

variable [Module (ZMod p) V]

/-- The actual additive Frobenius operator, regarded as a prime-field-linear map. -/
def frobeniusPrimeLinear : V →ₗ[ZMod p] V where
  toAddHom := F.toAddHom
  map_smul' a x := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    change F ((n : ZMod p) • x) = (n : ZMod p) • F x
    simp only [Int.cast_smul_eq_zsmul]
    exact map_zsmul F.toAddHom n x

@[simp]
theorem frobeniusPrimeLinear_apply (v : V) : frobeniusPrimeLinear p F v = F v := rfl

/-- Prime-field-independent fixed vectors remain independent over the whole field. -/
theorem linearIndependent_of_frobenius_fixed {ι : Type*} {v : ι → V}
    (hv : ∀ i, F (v i) = v i) (h : LinearIndependent (ZMod p) v) :
    LinearIndependent k v := by
  classical
  have aux (s : Finset ι) :
      LinearIndepOn (ZMod p) v (s : Set ι) → LinearIndepOn k v (s : Set ι) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.coe_insert]
        intro hs
        have hs' := (linearIndepOn_insert (K := ZMod p) hi).mp hs
        have hsk := ih hs'.1
        apply hsk.insert
        intro hmem
        obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun k (v := v)).mp hmem
        have hcF : ∑ j : s, c j ^ p • v j = v i := by
          simpa only [map_sum, map_smulₛₗ, _root_.frobenius_def, hv] using congrArg F hc
        have hcfix (j : s) : c j ^ p = c j :=
          hsk.eq_coords_of_eq (hcF.trans hc.symm) j
        have hcint (j : s) : ∃ n : ℤ, (n : k) = c j :=
          (mem_bot_iff_intCast p k).mp
            ((Subfield.mem_bot_iff_pow_eq_self k p).mpr (hcfix j))
        choose a ha using hcint
        apply hs'.2
        apply (Submodule.mem_span_image_finset_iff_exists_fun (ZMod p) (v := v)).mpr
        refine ⟨fun j => (a j : ZMod p), ?_⟩
        calc
          ∑ j : s, (a j : ZMod p) • v j = ∑ j : s, (a j : k) • v j := by
            simp only [Int.cast_smul_eq_zsmul]
          _ = v i := by simp only [ha]; exact hc
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  exact aux s (h.comp _ Subtype.val_injective)

/-- The fixed prime-field submodule is finite dimensional. -/
theorem finiteDimensional_frobenius_fixedSubmodule [FiniteDimensional k V] :
    FiniteDimensional (ZMod p) (frobeniusPrimeLinear p F).fixedSubmodule := by
  let W := (frobeniusPrimeLinear p F).fixedSubmodule
  let b := Module.Basis.ofVectorSpace (ZMod p) W
  have h : LinearIndependent (ZMod p) (fun i => (b i : V)) :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hk : LinearIndependent k (fun i => (b i : V)) :=
    linearIndependent_of_frobenius_fixed p F (fun i => (b i).property) h
  let : Finite (Module.Basis.ofVectorSpaceIndex (ZMod p) W) := hk.finite
  exact Module.Finite.of_basis b

/-- The fixed prime-field dimension is bounded by the ambient field dimension. -/
theorem finrank_frobenius_fixedSubmodule_le [FiniteDimensional k V] :
    Module.finrank (ZMod p) (frobeniusPrimeLinear p F).fixedSubmodule ≤
      Module.finrank k V := by
  let W := (frobeniusPrimeLinear p F).fixedSubmodule
  let := finiteDimensional_frobenius_fixedSubmodule p F
  let b := Module.finBasis (ZMod p) W
  have h : LinearIndependent (ZMod p) (fun i => (b i : V)) :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hk : LinearIndependent k (fun i => (b i : V)) :=
    linearIndependent_of_frobenius_fixed p F (fun i => (b i).property) h
  simpa using hk.fintype_card_le_finrank

end PrimeScalars

/-- A Frobenius-semilinear endomorphism in finite dimension has finitely many fixed vectors. -/
theorem finite_fixedPoints_of_frobenius [FiniteDimensional k V] :
    Finite {v : V // F v = v} := by
  let : Module (ZMod p) V := Module.compHom V (ZMod.castHom dvd_rfl k)
  let := finiteDimensional_frobenius_fixedSubmodule p F
  change Finite (frobeniusPrimeLinear p F).fixedSubmodule
  exact Module.finite_of_finite (ZMod p)

end LinearMap
