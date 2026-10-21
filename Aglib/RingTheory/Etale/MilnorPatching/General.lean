/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Etale.MilnorPatching.Unramified

/-!
# Canonical reconstruction for general Milnor patching

The rings and maps are the literal fibre products from `MilnorPatching`.
The component tensor comparisons retain their specified pure-tensor maps.
The reconstruction argument uses the conductor and requires no finite-module,
Noetherian, or flatness hypothesis.

The mathematical reference is Stacks Project, Tags 08KH and 07RU. The broader
etale theorem in Tag 08KQ uses the flatness and finite-presentation descent
proved in the upper companion leaves; the parent proposition is not assumed here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace RingHom.Etale.MilnorPatching.General

universe u

variable (R S T : Type u) {C D U : Type u}
  [CommRing R] [CommRing S] [CommRing T]
  [CommRing C] [CommRing D] [CommRing U]
  [Algebra R T] [Algebra S T] [Algebra R C] [Algebra S D] [Algebra T U]
  (b : C →+* U) (v : D →+* U)
  [hb : Fact (b.comp (algebraMap R C) = (algebraMap T U).comp (algebraMap R T))]
  [hv : Fact (v.comp (algebraMap S D) = (algebraMap T U).comp (algebraMap S T))]

local notation "P" => fiberRing (algebraMap R T) (algebraMap S T)
local notation "Q" => fiberRing b v
local notation "α" => fiberMap (algebraMap R T) (algebraMap S T)
  (algebraMap R C) (algebraMap S D) (algebraMap T U) b v hb.out hv.out

attribute [local instance] FiniteFree.fstAlgebra FiniteFree.sndAlgebra

/-- The original fibre-product map gives the local algebra action on the upper fibre ring. -/
local instance fiberAlgebra : Algebra P Q := (α).toAlgebra
variable [hPC : Algebra (fiberRing (algebraMap R T) (algebraMap S T)) C]
  [hPD : Algebra (fiberRing (algebraMap R T) (algebraMap S T)) D]
  [hPCR : IsScalarTower (fiberRing (algebraMap R T) (algebraMap S T)) R C]
  [hPSD : IsScalarTower (fiberRing (algebraMap R T) (algebraMap S T)) S D]

/-- The two equal boundary composites give the local action on the common boundary ring. -/
local instance boundaryAlgebra : Algebra P T :=
  ((algebraMap R T).comp (RingHom.pullbackFst (algebraMap R T)
    (algebraMap S T))).toAlgebra
/-- The first projection retains the original boundary scalar tower. -/
local instance boundaryFstTower : IsScalarTower P R T :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
/-- The second projection retains the same boundary scalar tower. -/
local instance boundarySndTower : IsScalarTower P S T :=
  IsScalarTower.of_algebraMap_eq fun p => p.property

/-- The actual first projection, with the original fibre-base scalar action. -/
def fstAlgHom : Q →ₐ[P] C where
  __ := RingHom.pullbackFst b v
  commutes' p := (IsScalarTower.algebraMap_apply P R C p).symm

/-- The actual second projection, with the original fibre-base scalar action. -/
def sndAlgHom : Q →ₐ[P] D where
  __ := RingHom.pullbackSnd b v
  commutes' p := (IsScalarTower.algebraMap_apply P S D p).symm

/-- The canonical first-component tensor comparison. -/
def fstTensorHom : R ⊗[P] Q →ₐ[R] C :=
  AlgHom.liftEquiv P R Q C (fstAlgHom R S T b v)

/-- The canonical second-component tensor comparison. -/
def sndTensorHom : S ⊗[P] Q →ₐ[S] D :=
  AlgHom.liftEquiv P S Q D (sndAlgHom R S T b v)

omit hPD hPSD in
@[simp]
theorem fstTensorHom_tmul (a : R) (q : Q) :
    fstTensorHom R S T b v (a ⊗ₜ[P] q) = a • q.val.1 := rfl

omit hPC hPCR in
@[simp]
theorem sndTensorHom_tmul (a : S) (q : Q) :
    sndTensorHom R S T b v (a ⊗ₜ[P] q) = a • q.val.2 := rfl

omit hPC hPD hPCR hPSD in
private theorem conductor_mul_mem
    (hgen : Submodule.span R (Set.range (fun q : Q => q.val.1)) = ⊤)
    (c : C) :
    ∀ a ∈ RingHom.ker (algebraMap R T),
      ∃ q ∈ (RingHom.ker (algebraMap P S)).map α,
        q.val.1 = algebraMap R C a * c ∧ q.val.2 = 0 := by
  let K := (RingHom.ker (algebraMap P S)).map α
  have hc : c ∈ Submodule.span R (Set.range (fun q : Q => q.val.1)) := by
    rw [hgen]
    trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨q, rfl⟩ := hc
    intro a ha
    let p : P := ⟨(a, 0), by
      change algebraMap R T a = algebraMap S T 0
      simpa using ha⟩
    have hp : α p ∈ K := Ideal.mem_map_of_mem α (by change (0 : S) = 0; rfl)
    refine ⟨α p * q, K.mul_mem_right q hp, rfl, ?_⟩
    change algebraMap S D 0 * q.val.2 = 0
    simp
  | zero =>
    intro a ha
    exact ⟨0, K.zero_mem, by simp, rfl⟩
  | add c d hc hd ihc ihd =>
    intro a ha
    obtain ⟨q, hq, hqc, hq0⟩ := ihc a ha
    obtain ⟨q', hq', hqd, hq'0⟩ := ihd a ha
    exact ⟨q + q', K.add_mem hq hq', by simpa [mul_add] using congrArg₂ (· + ·) hqc hqd,
      by change q.val.2 + q'.val.2 = 0; rw [hq0, hq'0, add_zero]⟩
  | smul a' c hc ih =>
    intro a ha
    obtain ⟨q, hq, hq1, hq0⟩ := ih (a * a')
      (by change algebraMap R T (a * a') = 0; rw [map_mul, ha, zero_mul])
    exact ⟨q, hq, by simpa [Algebra.smul_def, map_mul, mul_assoc] using hq1, hq0⟩

omit hPC hPD hPCR hPSD in
/-- The second-projection kernel is the extension of the original conductor.
This uses both displayed tensor comparisons but no flatness. -/
theorem ker_snd_eq_map
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) :
    RingHom.ker (algebraMap Q D) =
      (RingHom.ker (algebraMap P S)).map α := by
  let K := (RingHom.ker (algebraMap P S)).map α
  have hgen := span_fst_fiberRing_eq_top hf b v hb.out eC eD heC heD
  have hker := ker_boundary_of_tensorEquiv hf b eC heC
  have hmem (c : C) (hc : c ∈ (RingHom.ker (algebraMap R T)).map (algebraMap R C)) :
      ∀ z : C, ∃ q ∈ K, q.val.1 = z * c ∧ q.val.2 = 0 := by
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a, ha, rfl⟩ := hc
      intro z
      obtain ⟨q, hq, hq1, hq0⟩ := conductor_mul_mem R S T b v hgen z a ha
      exact ⟨q, hq, by simpa only [mul_comm] using hq1, hq0⟩
    | zero =>
      intro z
      exact ⟨0, K.zero_mem, by simp, rfl⟩
    | add c d hc hd ihc ihd =>
      intro z
      obtain ⟨q, hq, hq1, hq0⟩ := ihc z
      obtain ⟨q', hq', hq'1, hq'0⟩ := ihd z
      exact ⟨q + q', K.add_mem hq hq', by simpa [mul_add] using congrArg₂ (· + ·) hq1 hq'1,
        by change q.val.2 + q'.val.2 = 0; rw [hq0, hq'0, add_zero]⟩
    | smul a c hc ih =>
      intro z
      simpa only [smul_eq_mul, mul_assoc] using ih (z * a)
  apply le_antisymm
  · intro q hq
    have hq0 : q.val.2 = 0 := hq
    have hq1 : q.val.1 ∈ (RingHom.ker (algebraMap R T)).map (algebraMap R C) := by
      rw [← hker]
      change b q.val.1 = 0
      rw [show b q.val.1 = v q.val.2 from q.property, hq0, map_zero]
    obtain ⟨q', hq', hq'1, hq'0⟩ := hmem q.val.1 hq1 1
    have heq : q' = q := by
      apply Subtype.ext
      exact Prod.ext (by simpa using hq'1) (hq'0.trans hq0.symm)
    exact heq ▸ hq'
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change algebraMap S D p.val.2 = 0
    have hp0 : p.val.2 = 0 := hp
    rw [hp0, map_zero]

omit hPC hPCR in
/-- The second-component comparison is bijective for arbitrary compatible
component algebras. -/
theorem sndTensorHom_bijective
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) :
    Function.Bijective (sndTensorHom R S T b v) := by
  have hπ : Function.Surjective (algebraMap P S) :=
    RingHom.surjective_pullbackSnd_of_surjective _ _ hf
  have hq : Function.Surjective (algebraMap Q D) :=
    RingHom.surjective_pullbackSnd_of_surjective b v
      (surjective_boundary_of_tensorEquiv hf b eC heC)
  let E := quotientBoundaryEquiv (C := Q) hπ (AlgEquiv.refl : S ⊗[P] Q ≃ₐ[S] S ⊗[P] Q)
  let F := (Ideal.quotEquivOfEq
    (ker_snd_eq_map R S T b v hf eC eD heC heD).symm).trans
      (RingHom.quotientKerEquivOfSurjective hq)
  have hEF (z : Q ⧸ (RingHom.ker (algebraMap P S)).map (algebraMap P Q)) :
      sndTensorHom R S T b v (E z) = F z := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [quotientBoundaryEquiv_mk]
    change (1 : S) • q.val.2 = F (Ideal.Quotient.mk _ q)
    rw [one_smul]
    rfl
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := E.surjective x
    obtain ⟨y, rfl⟩ := E.surjective y
    exact congrArg E (F.injective ((hEF x).symm.trans (hxy.trans (hEF y))))
  · intro d
    obtain ⟨z, rfl⟩ := F.surjective d
    exact ⟨E z, hEF z⟩

/-- The second-component algebra is the actual tensor base change. -/
def sndTensorEquiv
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) : S ⊗[P] Q ≃ₐ[S] D :=
  AlgEquiv.ofBijective (sndTensorHom R S T b v)
    (sndTensorHom_bijective R S T b v hf eC eD heC heD)

omit hPC hPCR in
@[simp]
theorem sndTensorEquiv_tmul
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) (a : S) (q : Q) :
    sndTensorEquiv R S T b v hf eC eD heC heD (a ⊗ₜ[P] q) = a • q.val.2 := rfl

omit hPD hPSD in
/-- The first-component comparison is surjective for arbitrary compatible
component algebras. -/
theorem fstTensorHom_surjective
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) :
    Function.Surjective (fstTensorHom R S T b v) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← span_fst_fiberRing_eq_top hf b v hb.out eC eD heC heD]
  apply Submodule.span_le.mpr
  rintro c ⟨q, rfl⟩
  exact ⟨1 ⊗ₜ[P] q, by
    change (1 : R) • q.val.1 = q.val.1
    exact one_smul R _⟩

omit hPC hPD hPCR hPSD in
private theorem tensor_conductor_mem (x : R ⊗[P] Q)
    (hx : x ∈ (RingHom.ker (algebraMap R T)).map
      (Algebra.TensorProduct.includeLeft : R →ₐ[P] R ⊗[P] Q)) :
    ∃ q : Q, q.val.2 = 0 ∧ (1 : R) ⊗ₜ[P] q = x := by
  have h (x : R ⊗[P] Q)
      (hx : x ∈ (RingHom.ker (algebraMap R T)).map
        (Algebra.TensorProduct.includeLeft : R →ₐ[P] R ⊗[P] Q)) :
      ∀ z : R ⊗[P] Q, ∃ q : Q, q.val.2 = 0 ∧ (1 : R) ⊗ₜ[P] q = z * x := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a' q =>
        let p : P := ⟨(a' * a, 0), by
          change algebraMap R T (a' * a) = algebraMap S T 0
          rw [map_mul, ha, mul_zero, map_zero]⟩
        refine ⟨α p * q, ?_, ?_⟩
        · change algebraMap S D 0 * q.val.2 = 0
          simp
        · change (1 : R) ⊗ₜ[P] (α p * q) =
            (a' ⊗ₜ[P] q) * (a ⊗ₜ[P] (1 : Q))
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          have hpR : algebraMap P R p = a' * a := rfl
          have hpQ : algebraMap P Q p = α p := rfl
          simpa only [Algebra.smul_def, mul_one, hpR, hpQ] using
            (TensorProduct.smul_tmul p (1 : R) q).symm
      | add z w ihz ihw =>
        obtain ⟨q, hq0, hq⟩ := ihz
        obtain ⟨q', hq'0, hq'⟩ := ihw
        refine ⟨q + q', ?_, ?_⟩
        · change q.val.2 + q'.val.2 = 0
          rw [hq0, hq'0, add_zero]
        · rw [TensorProduct.tmul_add, hq, hq', add_mul]
    | zero =>
      intro z
      exact ⟨0, rfl, by simp⟩
    | add x y hx hy ihx ihy =>
      intro z
      obtain ⟨q, hq0, hq⟩ := ihx z
      obtain ⟨q', hq'0, hq'⟩ := ihy z
      refine ⟨q + q', ?_, ?_⟩
      · change q.val.2 + q'.val.2 = 0
        rw [hq0, hq'0, add_zero]
      · rw [TensorProduct.tmul_add, hq, hq', mul_add]
    | smul a x hx ih =>
      intro z
      simpa only [smul_eq_mul, mul_assoc] using ih (z * a)
  simpa only [one_mul] using h x hx 1

/-- The first-component comparison is bijective for arbitrary compatible
component algebras. The injectivity proof is a conductor calculation. -/
theorem fstTensorHom_bijective
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) :
    Function.Bijective (fstTensorHom R S T b v) := by
  let E : T ⊗[P] Q ≃ₐ[T] U :=
    ((Algebra.TensorProduct.cancelBaseChange P S T T Q).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T)
        (sndTensorEquiv R S T b v hf eC eD heC heD))).trans eD
  let π : R ⊗[P] Q →ₐ[P] T ⊗[P] Q :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom P R T) (AlgHom.id P Q)
  have hE (a : T) (q : Q) : E (a ⊗ₜ[P] q) = algebraMap T U a * v q.val.2 := by
    simp only [E, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, sndTensorEquiv_tmul, one_smul]
    change eD (a ⊗ₜ[S] q.val.2) = algebraMap T U a * v q.val.2
    calc
      eD (a ⊗ₜ[S] q.val.2) = eD (a • (1 ⊗ₜ[S] q.val.2)) := by
        rw [TensorProduct.smul_tmul']
        simp
      _ = algebraMap T U a * v q.val.2 := by rw [map_smul, heD, Algebra.smul_def]
  have hπ (x : R ⊗[P] Q) : E (π x) = b (fstTensorHom R S T b v x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a q =>
      change E (algebraMap R T a ⊗ₜ[P] q) = b (a • q.val.1)
      rw [hE, Algebra.smul_def, map_mul]
      rw [show b (algebraMap R C a) = algebraMap T U (algebraMap R T a) from
        RingHom.congr_fun hb.out a]
      rw [show b q.val.1 = v q.val.2 from q.property]
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  have hker : RingHom.ker π = (RingHom.ker (algebraMap R T)).map
      (Algebra.TensorProduct.includeLeft : R →ₐ[P] R ⊗[P] Q) :=
    Algebra.TensorProduct.rTensor_ker (IsScalarTower.toAlgHom P R T) hf
  have hzero (x : R ⊗[P] Q) (hx : fstTensorHom R S T b v x = 0) : x = 0 := by
    have hπx : π x = 0 := E.injective (by rw [hπ, hx, map_zero, map_zero])
    have hxI : x ∈ (RingHom.ker (algebraMap R T)).map
        (Algebra.TensorProduct.includeLeft : R →ₐ[P] R ⊗[P] Q) := by
      rw [← hker]
      exact hπx
    obtain ⟨q, hq0, hqx⟩ := tensor_conductor_mem R S T b v x hxI
    have hq1 : q.val.1 = 0 := by
      have h := congrArg (fstTensorHom R S T b v) hqx
      simpa only [fstTensorHom_tmul, one_smul, hx] using h
    have hq : q = 0 := Subtype.ext (Prod.ext hq1 hq0)
    simpa only [hq, TensorProduct.tmul_zero] using hqx.symm
  refine ⟨?_, fstTensorHom_surjective R S T b v hf eC eD heC heD⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

/-- The first-component algebra is the actual tensor base change. -/
def fstTensorEquiv
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) : R ⊗[P] Q ≃ₐ[R] C :=
  AlgEquiv.ofBijective (fstTensorHom R S T b v)
    (fstTensorHom_bijective R S T b v hf eC eD heC heD)

@[simp]
theorem fstTensorEquiv_tmul
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) (a : R) (q : Q) :
    fstTensorEquiv R S T b v hf eC eD heC heD (a ⊗ₜ[P] q) = a • q.val.1 := rfl

/-- Formal unramifiedness descends through the literal Milnor square for
arbitrary compatible component algebras. -/
theorem formallyUnramified_fiberMap
    [Algebra.FormallyUnramified R C] [Algebra.FormallyUnramified S D]
    (hf : Function.Surjective (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) : (α).FormallyUnramified := by
  change Algebra.FormallyUnramified P Q
  constructor
  have hR : Subsingleton (R ⊗[P] Ω[Q⁄P]) := by
    let : Algebra.FormallyUnramified R (R ⊗[P] Q) :=
      Algebra.FormallyUnramified.of_equiv
        (fstTensorEquiv R S T b v hf eC eD heC heD).symm
    let : Algebra Q (R ⊗[P] Q) := Algebra.TensorProduct.rightAlgebra
    exact (KaehlerDifferential.tensorKaehlerEquivBase P R Q (R ⊗[P] Q)).subsingleton
  have hS : Subsingleton (S ⊗[P] Ω[Q⁄P]) := by
    let : Algebra.FormallyUnramified S (S ⊗[P] Q) :=
      Algebra.FormallyUnramified.of_equiv
        (sndTensorEquiv R S T b v hf eC eD heC heD).symm
    let : Algebra Q (S ⊗[P] Q) := Algebra.TensorProduct.rightAlgebra
    exact (KaehlerDifferential.tensorKaehlerEquivBase P S Q (S ⊗[P] Q)).subsingleton
  let := hR
  let := hS
  exact subsingleton_of_tensor_components (algebraMap R T) (algebraMap S T) hf Ω[Q⁄P]

end RingHom.Etale.MilnorPatching.General

namespace RingHom.Etale.MilnorPatching

attribute [local instance] FiniteFree.fstAlgebra FiniteFree.sndAlgebra

universe u

variable {R S T C D U : Type u}
  [CommRing R] [CommRing S] [CommRing T]
  [CommRing C] [CommRing D] [CommRing U]

/-- Formal unramifiedness for the original seven-map tensor-compatible Milnor
square. The original ring homomorphisms and their scalar actions are preserved. -/
theorem formallyUnramified_fiberMap
    (f : R →+* T) (g : S →+* T) (r : R →+* C) (s : S →+* D)
    (t : T →+* U) (b : C →+* U) (v : D →+* U)
    (hc : b.comp r = t.comp f) (hd : v.comp s = t.comp g) :
    letI : Algebra R T := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra R C := r.toAlgebra
    letI : Algebra S D := s.toAlgebra
    letI : Algebra T U := t.toAlgebra
    ∀ (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U),
      (∀ c, eC (1 ⊗ₜ[R] c) = b c) →
      (∀ d, eD (1 ⊗ₜ[S] d) = v d) →
      Function.Surjective f → r.FormallyUnramified → s.FormallyUnramified →
      (fiberMap f g r s t b v hc hd).FormallyUnramified := by
  let : Algebra R T := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R C := r.toAlgebra
  let : Algebra S D := s.toAlgebra
  let : Algebra T U := t.toAlgebra
  intro eC eD heC heD hf hr hs
  let : Algebra.FormallyUnramified R C := hr
  let : Algebra.FormallyUnramified S D := hs
  let : Fact (b.comp (algebraMap R C) = (algebraMap T U).comp (algebraMap R T)) := ⟨hc⟩
  let : Fact (v.comp (algebraMap S D) = (algebraMap T U).comp (algebraMap S T)) := ⟨hd⟩
  let : Algebra (fiberRing f g) C := (r.comp (RingHom.pullbackFst f g)).toAlgebra
  let : Algebra (fiberRing f g) D := (s.comp (RingHom.pullbackSnd f g)).toAlgebra
  let : IsScalarTower (fiberRing f g) R C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (fiberRing f g) S D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact General.formallyUnramified_fiberMap R S T b v hf eC eD heC heD

/-- Flatness and finite presentation of the original map give etale patching
together with the proved formal-unramifiedness comparison. The upper companion
leaves supply both conditions from the component data. -/
theorem etale_fiberMap_of_flat_of_finitePresentation
    (f : R →+* T) (g : S →+* T) (r : R →+* C) (s : S →+* D)
    (t : T →+* U) (b : C →+* U) (v : D →+* U)
    (hc : b.comp r = t.comp f) (hd : v.comp s = t.comp g) :
    letI : Algebra R T := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra R C := r.toAlgebra
    letI : Algebra S D := s.toAlgebra
    letI : Algebra T U := t.toAlgebra
    ∀ (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U),
      (∀ c, eC (1 ⊗ₜ[R] c) = b c) →
      (∀ d, eD (1 ⊗ₜ[S] d) = v d) →
      Function.Surjective f → r.Etale → s.Etale →
      (fiberMap f g r s t b v hc hd).Flat →
      (fiberMap f g r s t b v hc hd).FinitePresentation →
      (fiberMap f g r s t b v hc hd).Etale := by
  intro eC eD heC heD hf hr hs hflat hfp
  exact RingHom.Etale.iff_flat_and_formallyUnramified.mpr
    ⟨hflat, formallyUnramified_fiberMap f g r s t b v hc hd eC eD heC heD hf
      hr.formallyUnramified hs.formallyUnramified, hfp⟩

end RingHom.Etale.MilnorPatching
