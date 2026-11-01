/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Ideal.Operations

/-! # Original open thickenings of a split affine algebra

An arbitrary open and its intersection with the section have identical inverse
images on every original kernel-power quotient. Only point maps agree; the
scheme maps to the ambient affine scheme need not agree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (i : A →+* B) (ε : B →+* A) (hε : ε.comp i = RingHom.id A)

/-- The original quotient map to the ambient affine scheme. -/
abbrev splitQuotientMap (n : ℕ) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker ε) ^ n)))

/-- The original scalar map of the kernel-power quotient. -/
abbrev splitQuotientScalar (n : ℕ) :=
  Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk ((RingHom.ker ε) ^ n)).comp i))

include hε in
/-- The quotient and section-composite have the same original point map,
including the empty zeroth quotient. -/
theorem splitQuotient_point_eq (n : ℕ)
    (p : (Spec (.of (B ⧸ (RingHom.ker ε) ^ n)) : Scheme)) :
    splitQuotientMap ε n p =
      Spec.map (CommRingCat.ofHom ε) (splitQuotientScalar i ε n p) := by
  let P := PrimeSpectrum.comap (Ideal.Quotient.mk ((RingHom.ker ε) ^ n)) p
  have hk : RingHom.ker ε ≤ P.asIdeal := Ideal.IsPrime.le_of_pow_le (by
    intro b hb
    change Ideal.Quotient.mk ((RingHom.ker ε) ^ n) b ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb]
    exact p.asIdeal.zero_mem)
  have he (a : A) : ε (i a) = a := DFunLike.congr_fun hε a
  apply PrimeSpectrum.ext
  ext b
  change b ∈ P.asIdeal ↔ i (ε b) ∈ P.asIdeal
  have hd : b - i (ε b) ∈ P.asIdeal := hk (by
    change ε (b - i (ε b)) = 0
    rw [map_sub, he, sub_self])
  constructor
  · intro hb
    simpa only [sub_sub_cancel] using P.asIdeal.sub_mem hb hd
  · intro hb
    simpa only [sub_add_cancel] using P.asIdeal.add_mem hd hb

include hε in
/-- Equality of the original inverse-image opens, not an assumption that the
ambient open comes from the base. -/
theorem splitQuotient_preimage_eq (V : (Spec (.of B)).Opens) (n : ℕ) :
    splitQuotientMap ε n ⁻¹ᵁ V =
      splitQuotientScalar i ε n ⁻¹ᵁ (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V) := by
  ext p
  change splitQuotientMap ε n p ∈ V ↔
    Spec.map (CommRingCat.ofHom ε) (splitQuotientScalar i ε n p) ∈ V
  rw [splitQuotient_point_eq i ε hε]

/-- The literal two open pullbacks are isomorphic over the same quotient scheme. -/
def splitQuotientOpenIso (V : (Spec (.of B)).Opens) (n : ℕ) :
    pullback V.ι (splitQuotientMap ε n) ≅
      pullback (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V).ι (splitQuotientScalar i ε n) :=
  IsOpenImmersion.isoOfRangeEq (pullback.snd _ _) (pullback.snd _ _) (by
    rw [IsOpenImmersion.range_pullbackSnd, IsOpenImmersion.range_pullbackSnd,
      Opens.opensRange_ι, Opens.opensRange_ι, splitQuotient_preimage_eq i ε hε V n])

@[reassoc (attr := simp)]
theorem splitQuotientOpenIso_hom_snd (V : (Spec (.of B)).Opens) (n : ℕ) :
    (splitQuotientOpenIso i ε hε V n).hom ≫ pullback.snd _ _ =
      pullback.snd V.ι (splitQuotientMap ε n) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The second original projection triangle. -/
@[reassoc]
theorem splitQuotientOpenIso_hom_fst_ι (V : (Spec (.of B)).Opens) (n : ℕ) :
    (splitQuotientOpenIso i ε hε V n).hom ≫ pullback.fst _ _ ≫
        (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V).ι =
      pullback.snd V.ι (splitQuotientMap ε n) ≫ splitQuotientScalar i ε n := by
  rw [pullback.condition, splitQuotientOpenIso_hom_snd_assoc]

/-- Original quotient reduction on the ambient-open pullback. -/
def splitQuotientOpenReduction (V : (Spec (.of B)).Opens) {m n : ℕ} (h : m ≤ n) :
    pullback V.ι (splitQuotientMap ε m) ⟶ pullback V.ι (splitQuotientMap ε n) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right h : (RingHom.ker ε)^n ≤ (RingHom.ker ε)^m)))) (by
        rw [Category.assoc, ← Spec.map_comp]
        exact pullback.condition)

@[reassoc (attr := simp)]
theorem splitQuotientOpenReduction_snd (V : (Spec (.of B)).Opens)
    {m n : ℕ} (h : m ≤ n) :
    splitQuotientOpenReduction ε V h ≫ pullback.snd _ _ =
      pullback.snd V.ι (splitQuotientMap ε m) ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right h :
          (RingHom.ker ε)^n ≤ (RingHom.ker ε)^m))) := pullback.lift_snd _ _ _

/-- The original quotient reduction on the base-open pullback. -/
def splitQuotientScalarReduction (U : (Spec (.of A)).Opens) {m n : ℕ} (h : m ≤ n) :
    pullback U.ι (splitQuotientScalar i ε m) ⟶
      pullback U.ι (splitQuotientScalar i ε n) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right h : (RingHom.ker ε)^n ≤ (RingHom.ker ε)^m)))) (by
        rw [Category.assoc, ← Spec.map_comp]
        exact pullback.condition)

@[reassoc (attr := simp)]
theorem splitQuotientScalarReduction_snd (U : (Spec (.of A)).Opens)
    {m n : ℕ} (h : m ≤ n) :
    splitQuotientScalarReduction i ε U h ≫ pullback.snd _ _ =
      pullback.snd U.ι (splitQuotientScalar i ε m) ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right h :
          (RingHom.ker ε)^n ≤ (RingHom.ker ε)^m))) := pullback.lift_snd _ _ _

/-- The comparison commutes with the original reductions on both pullbacks. -/
@[reassoc]
theorem splitQuotientOpenIso_reduction (V : (Spec (.of B)).Opens)
    {m n : ℕ} (h : m ≤ n) :
    splitQuotientOpenReduction ε V h ≫ (splitQuotientOpenIso i ε hε V n).hom =
      (splitQuotientOpenIso i ε hε V m).hom ≫
        splitQuotientScalarReduction i ε (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V) h := by
  apply (cancel_mono (pullback.snd (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V).ι
    (splitQuotientScalar i ε n))).mp
  simp

/-- Transported reduction retains the whole original quotient map. This law
uniquely specifies the reduction on the base-open pullbacks. -/
@[reassoc]
theorem splitQuotientOpenIso_reduction_snd (V : (Spec (.of B)).Opens)
    {m n : ℕ} (h : m ≤ n) :
    (splitQuotientOpenIso i ε hε V m).inv ≫ splitQuotientOpenReduction ε V h ≫
        (splitQuotientOpenIso i ε hε V n).hom ≫ pullback.snd _ _ =
      pullback.snd (Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V).ι (splitQuotientScalar i ε m) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right h :
          (RingHom.ker ε)^n ≤ (RingHom.ker ε)^m))) := by
  rw [splitQuotientOpenIso_hom_snd, splitQuotientOpenReduction_snd]
  rw [← splitQuotientOpenIso_hom_snd i ε hε V m]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme
