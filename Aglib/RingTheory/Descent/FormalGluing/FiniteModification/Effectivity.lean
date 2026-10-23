/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Descent.FormalGluing.FiniteModification.Torsion
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Actual tensor and finite-algebra assembly for formal gluing

Flat scalar extension preserves the actual algebra of compatible pairs,
through the native tensor equalizer and product comparisons. Bounded
quotient counits and the constructed regular-conductor model then supply
finite models with their original algebra and localization maps.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Algebra.Descent.FormalGluing

section EqualizerTransport

variable {S A B A' B' : Type*}
  [CommRing S] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra S A] [Algebra S B] [Algebra S A'] [Algebra S B']

/-- Restriction of the actual two ambient algebra equivalences to the
actual equalizers, using their original commuting squares. -/
def equalizerTransport (eA : A ≃ₐ[S] A') (eB : B ≃ₐ[S] B')
    (f g : A →ₐ[S] B) (f' g' : A' →ₐ[S] B')
    (hf : ∀ x, eB (f x) = f' (eA x)) (hg : ∀ x, eB (g x) = g' (eA x)) :
    AlgHom.equalizer f g ≃ₐ[S] AlgHom.equalizer f' g' where
  toFun x := ⟨eA x, (hf x).symm.trans ((congrArg eB x.property).trans (hg x))⟩
  invFun y := ⟨eA.symm y, by
    apply eB.injective
    rw [hf, hg, eA.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (eA.symm_apply_apply x)
  right_inv y := Subtype.ext (eA.apply_symm_apply y)
  map_mul' x y := Subtype.ext (eA.map_mul x y)
  map_add' x y := Subtype.ext (eA.map_add x y)
  commutes' r := Subtype.ext (eA.commutes r)

@[simp]
theorem equalizerTransport_coe (eA : A ≃ₐ[S] A') (eB : B ≃ₐ[S] B')
    (f g : A →ₐ[S] B) (f' g' : A' →ₐ[S] B')
    (hf : ∀ x, eB (f x) = f' (eA x)) (hg : ∀ x, eB (g x) = g' (eA x))
    (x : AlgHom.equalizer f g) :
    (equalizerTransport eA eB f g f' g' hf hg x : A') = eA x := rfl

end EqualizerTransport

section TensorCompatiblePairs

variable {R S A B H : Type*} [CommRing R] [CommRing S] [CommRing A]
  [CommRing B] [CommRing H] [Algebra R S] [Algebra R A] [Algebra R B] [Algebra R H]

/-- The actual fibre product of two algebra maps, realized as a subalgebra
of their product with its original coordinate maps. -/
def compatiblePairAlgebra (f : A →ₐ[R] H) (g : B →ₐ[R] H) : Subalgebra R (A × B) :=
  AlgHom.equalizer (f.comp (AlgHom.fst R A B)) (g.comp (AlgHom.snd R A B))

/-- Noetherian finiteness of this actual algebra follows from its original
inclusion in the finite product module. -/
theorem finite_compatiblePairAlgebra [IsNoetherianRing R]
    [Module.Finite R A] [Module.Finite R B] (f : A →ₐ[R] H) (g : B →ₐ[R] H) :
    Module.Finite R (compatiblePairAlgebra f g) := by
  let : Module.Finite R (compatiblePairAlgebra f g).toSubmodule := inferInstance
  exact Module.Finite.equiv (compatiblePairAlgebra f g).toSubmoduleEquiv

/-- The literal first-coordinate square for tensor and product commutes. -/
theorem tensorCompatiblePair_fst (f : A →ₐ[R] H)
    (z : S ⊗[R] (A × B)) :
    Algebra.TensorProduct.map (AlgHom.id S S) (f.comp (AlgHom.fst R A B)) z =
      Algebra.TensorProduct.map (AlgHom.id S S) f
        (Algebra.TensorProduct.prodRight R S S A B z).1 := by
  induction z using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy =>
      simpa only [map_add, Prod.fst_add] using congrArg₂ (fun x y => x + y) hx hy

/-- The literal second-coordinate square for tensor and product commutes. -/
theorem tensorCompatiblePair_snd (g : B →ₐ[R] H)
    (z : S ⊗[R] (A × B)) :
    Algebra.TensorProduct.map (AlgHom.id S S) (g.comp (AlgHom.snd R A B)) z =
      Algebra.TensorProduct.map (AlgHom.id S S) g
        (Algebra.TensorProduct.prodRight R S S A B z).2 := by
  induction z using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy =>
      simpa only [map_add, Prod.snd_add] using congrArg₂ (fun x y => x + y) hx hy

/-- Flat scalar extension preserves the actual compatible-pair algebra.
The proof combines the native algebra equalizer equivalence with the
actual tensor-product/product equivalence and its coordinate equations. -/
def tensorCompatiblePairEquiv [Module.Flat R S] (f : A →ₐ[R] H) (g : B →ₐ[R] H) :
    S ⊗[R] compatiblePairAlgebra f g ≃ₐ[S]
      compatiblePairAlgebra (Algebra.TensorProduct.map (AlgHom.id S S) f)
        (Algebra.TensorProduct.map (AlgHom.id S S) g) :=
  (AlgHom.tensorEqualizerEquiv S S (f.comp (AlgHom.fst R A B))
    (g.comp (AlgHom.snd R A B))).trans
      (equalizerTransport (Algebra.TensorProduct.prodRight R S S A B)
        (AlgEquiv.refl : (S ⊗[R] H) ≃ₐ[S] (S ⊗[R] H)) _ _ _ _
        (tensorCompatiblePair_fst f) (tensorCompatiblePair_snd g))

/-- The actual inclusion of the constructed comparison is the original
tensor map followed by the native tensor/product equivalence. -/
theorem tensorCompatiblePairEquiv_coe [Module.Flat R S]
    (f : A →ₐ[R] H) (g : B →ₐ[R] H) (z : S ⊗[R] compatiblePairAlgebra f g) :
    (tensorCompatiblePairEquiv f g z : (S ⊗[R] A) × (S ⊗[R] B)) =
      Algebra.TensorProduct.prodRight R S S A B
        (Algebra.TensorProduct.map (AlgHom.id S S) (compatiblePairAlgebra f g).val z) := by
  let F := f.comp (AlgHom.fst R A B)
  let G := g.comp (AlgHom.snd R A B)
  let F' := Algebra.TensorProduct.map (AlgHom.id S S) F
  let G' := Algebra.TensorProduct.map (AlgHom.id S S) G
  let e₁ := AlgHom.tensorEqualizerEquiv S S F G
  let e₂ := equalizerTransport (Algebra.TensorProduct.prodRight R S S A B)
    (AlgEquiv.refl : (S ⊗[R] H) ≃ₐ[S] (S ⊗[R] H)) F' G'
    ((Algebra.TensorProduct.map (AlgHom.id S S) f).comp
      (AlgHom.fst S (S ⊗[R] A) (S ⊗[R] B)))
    ((Algebra.TensorProduct.map (AlgHom.id S S) g).comp
      (AlgHom.snd S (S ⊗[R] A) (S ⊗[R] B)))
    (tensorCompatiblePair_fst f) (tensorCompatiblePair_snd g)
  have htrans : ((e₁.trans e₂) z : (S ⊗[R] A) × (S ⊗[R] B)) =
      (e₂ (e₁ z) : (S ⊗[R] A) × (S ⊗[R] B)) :=
    congrArg (fun x : compatiblePairAlgebra
      (Algebra.TensorProduct.map (AlgHom.id S S) f)
      (Algebra.TensorProduct.map (AlgHom.id S S) g) => x.val)
        (AlgEquiv.trans_apply e₁ e₂ z)
  have htransport : (e₂ (e₁ z) : (S ⊗[R] A) × (S ⊗[R] B)) =
      Algebra.TensorProduct.prodRight R S S A B (e₁ z : S ⊗[R] (A × B)) :=
    equalizerTransport_coe (Algebra.TensorProduct.prodRight R S S A B)
      (AlgEquiv.refl : (S ⊗[R] H) ≃ₐ[S] (S ⊗[R] H)) F' G' _ _
      (tensorCompatiblePair_fst f) (tensorCompatiblePair_snd g) (e₁ z)
  have hequalizer : (e₁ z : S ⊗[R] (A × B)) =
      (AlgHom.tensorEqualizer S S F G z : S ⊗[R] (A × B)) :=
    congrArg (fun x : AlgHom.equalizer F' G' => x.val)
      (AlgHom.tensorEqualizerEquiv_apply S S F G z)
  have hmap : (AlgHom.tensorEqualizer S S F G z : S ⊗[R] (A × B)) =
      Algebra.TensorProduct.map (AlgHom.id S S) (compatiblePairAlgebra f g).val z :=
    AlgHom.coe_tensorEqualizer S S F G z
  exact htrans.trans (htransport.trans
    (congrArg (Algebra.TensorProduct.prodRight R S S A B) (hequalizer.trans hmap)))

@[simp]
theorem tensorCompatiblePairEquiv_tmul [Module.Flat R S]
    (f : A →ₐ[R] H) (g : B →ₐ[R] H) (s : S) (x : compatiblePairAlgebra f g) :
    (tensorCompatiblePairEquiv f g (s ⊗ₜ[R] x) : (S ⊗[R] A) × (S ⊗[R] B)) =
      (s ⊗ₜ[R] x.val.1, s ⊗ₜ[R] x.val.2) := by
  have hmap : Algebra.TensorProduct.map (AlgHom.id S S)
      (compatiblePairAlgebra f g).val (s ⊗ₜ[R] x) = s ⊗ₜ[R] (x : A × B) :=
    Algebra.TensorProduct.map_tmul (AlgHom.id S S) (compatiblePairAlgebra f g).val s x
  exact (tensorCompatiblePairEquiv_coe f g (s ⊗ₜ[R] x)).trans
    ((congrArg (Algebra.TensorProduct.prodRight R S S A B) hmap).trans
      (Algebra.TensorProduct.prodRight_tmul R S S A B s (x : A × B)))

end TensorCompatiblePairs

section QuotientAnnihilation

variable {R S D : Type*} [CommRing R] [CommRing S] [CommRing D]
  [Algebra R S] [Algebra S D]

/-- An ideal whose actual extension lies in the quotient ideal annihilates
the original quotient module. -/
theorem quotient_smul_top_eq_bot (J : Ideal S) (K : Ideal D)
    (hJK : J.map (algebraMap S D) ≤ K) :
    J • (⊤ : Submodule S (D ⧸ K)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro s hs z _
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  change s • Ideal.Quotient.mk K x = 0
  rw [Algebra.smul_def]
  change Ideal.Quotient.mk K (algebraMap S D s) * Ideal.Quotient.mk K x = 0
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (K.mul_mem_right x (hJK (Ideal.mem_map_of_mem (algebraMap S D) hs)))

variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

/-- Annihilation by the actual extended source ideal gives the original
scalar annihilation equation. -/
theorem source_smul_eq_zero_of_extended_annihilation (J : Ideal R)
    (hM : J.map (algebraMap R S) • (⊤ : Submodule S M) = ⊥)
    (r : R) (hr : r ∈ J) (x : M) : r • x = 0 := by
  have hz := Submodule.smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R S) hr)
    (Submodule.mem_top : x ∈ (⊤ : Submodule S M))
  rw [hM] at hz
  simpa only [algebraMap_smul] using
    (show algebraMap R S r • x = 0 from hz)

end QuotientAnnihilation

section CompatiblePairLocalization

variable {R A B H : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing H]
  [Algebra R A] [Algebra R B] [Algebra R H]

/-- The original scalar map to compatible pairs is injective when its
first original coordinate is injective. -/
theorem compatiblePair_algebraMap_injective (F : A →ₐ[R] H) (G : B →ₐ[R] H)
    (hA : Function.Injective (algebraMap R A)) :
    Function.Injective (algebraMap R (compatiblePairAlgebra F G)) := by
  intro a b h
  apply hA
  exact congrArg (fun x : compatiblePairAlgebra F G => x.val.1) h

/-- A conductor power on the first coordinate and a killing power on the
second give an actual conductor power on the compatible-pair algebra. -/
theorem compatiblePair_power_conductor (F : A →ₐ[R] H) (G : B →ₐ[R] H)
    (f : R) (n m : ℕ)
    (hA : ∀ a : A, ∃ r : R, algebraMap R A r = f ^ n • a)
    (hB : ∀ b : B, f ^ m • b = 0) (x : compatiblePairAlgebra F G) :
    ∃ r : R, algebraMap R (compatiblePairAlgebra F G) r = f ^ (n + m) • x := by
  obtain ⟨r, hr⟩ := hA x.val.1
  refine ⟨f ^ m * r, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change algebraMap R A (f ^ m * r) = f ^ (n + m) • x.val.1
    rw [map_mul, ← Algebra.smul_def, hr, smul_smul, ← pow_add, Nat.add_comm m n]
  · change algebraMap R B (f ^ m * r) = f ^ (n + m) • x.val.2
    have hleft : algebraMap R B (f ^ m * r) = 0 := by
      rw [map_mul, ← Algebra.smul_def, hB]
    have hright : f ^ (n + m) • x.val.2 = 0 := by
      rw [pow_add, mul_smul, hB, smul_zero]
    exact hleft.trans hright.symm

/-- The original localization map to the constructed compatible-pair
algebra is bijective from these actual coordinate bounds. -/
theorem compatiblePair_localizationBaseMap_bijective
    (F : A →ₐ[R] H) (G : B →ₐ[R] H)
    (hAinj : Function.Injective (algebraMap R A)) (f : R) (n m : ℕ)
    (hA : ∀ a : A, ∃ r : R, algebraMap R A r = f ^ n • a)
    (hB : ∀ b : B, f ^ m • b = 0) :
    Function.Bijective (localizationBaseMap (S := compatiblePairAlgebra F G) f) := by
  constructor
  · change Function.Injective
      (Localization.awayMap (algebraMap R (compatiblePairAlgebra F G)) f)
    apply Localization.awayMap_injective_iff.mpr
    intro x hx
    have hx0 : x = 0 := compatiblePair_algebraMap_injective F G hAinj
      (by simpa only [map_zero] using hx)
    exact ⟨0, by simpa only [pow_zero, one_mul] using hx0⟩
  · change Function.Surjective
      (Localization.awayMap (algebraMap R (compatiblePairAlgebra F G)) f)
    apply Localization.awayMap_surjective_iff.mpr
    intro x
    obtain ⟨r, hr⟩ := compatiblePair_power_conductor F G f n m hA hB x
    exact ⟨r, n + m, by simpa only [Algebra.smul_def, map_pow] using hr⟩

end CompatiblePairLocalization

section FiniteModel

universe u

variable {R S D : Type u} [CommRing R] [CommRing S] [CommRing D]
  [Algebra R S] [Algebra R D] [Algebra S D] [IsScalarTower R S D]
  [IsNoetherianRing R] [IsNoetherianRing S]
  [Module.FaithfullyFlat R S] [Module.Finite S D]

/-- Actual finite-algebra effectivity from a regular source conductor.
The torsion quotient, regular-conductor model, finite quotient counits and
compatible-pair algebra are all constructed in the proof. The hypotheses
are original coefficient maps and conductor products, not a model or a
descent datum. The original localized scalar maps are bijective off `I`.

The all-power coefficient input is supplied by the actual completion
comparison in the completion consumer. The original-input theorem below
also derives it from the canonical mod-`I` comparison. -/
theorem exists_finite_model_of_regular_conductor (I : Ideal R) (n : ℕ) (t : R)
    (ht : t ∈ I ^ n) (hreg : IsSMulRegular R t)
    (hinj : Function.Injective (algebraMap S D))
    (hcond : ∀ s ∈ (I ^ n).map (algebraMap R S), ∀ z : D,
      ∃ a : S, algebraMap S D a = s • z)
    (hcoeff : ∀ m : ℕ, Function.Surjective
      ((Ideal.Quotient.mk ((I ^ m).map (algebraMap R S))).comp (algebraMap R S))) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E), Module.Finite R E ∧
      ∃ θ : S ⊗[R] E ≃ₐ[S] D,
        (∀ s : S, θ (s ⊗ₜ[R] (1 : E)) = algebraMap S D s) ∧
        ∀ f ∈ I, Function.Bijective (localizationBaseMap (S := E) f) := by
  classical
  obtain ⟨a, d, hd, hspan⟩ := exists_conductorFamily (I ^ n)
    (I ^ n).fg_of_isNoetherianRing t ht
  subst t
  let T := conductorTorsionIdeal (D := D) (algebraMap R S (d none))
  let D₀ := D ⧸ T
  have hregS : IsSMulRegular S (algebraMap R S (d none)) := hreg.of_flat
  have htS : algebraMap R S (d none) ∈ (I ^ n).map (algebraMap R S) :=
    Ideal.mem_map_of_mem (algebraMap R S) ht
  have hinj₀ : Function.Injective (algebraMap S D₀) :=
    conductorTorsionQuotient_algebraMap_injective _ hinj hregS
  have hreg₀ : IsSMulRegular D₀ (algebraMap R S (d none)) :=
    conductorTorsionQuotient_regular _ hinj hregS (hcond _ htS)
  have hcond₀ (i : Option (Fin a)) (z : D₀) :
      ∃ s : S, algebraMap S D₀ s = algebraMap R S (d i) • z := by
    apply conductorTorsionQuotient_conductor (algebraMap R S (d none))
      ((I ^ n).map (algebraMap R S)) hcond
    apply Ideal.mem_map_of_mem
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hcoeffn : Function.Surjective ((Ideal.Quotient.mk
      ((Ideal.span (Set.range d)).map (algebraMap R S))).comp (algebraMap R S)) := by
    rw [hspan]
    exact hcoeff n
  let E₀ := regularConductorSubalgebra (d none) hinj₀ (hcond₀ none)
  let ψ₀ : E₀ →ₐ[R] D₀ := regularConductorMap (d none) hinj₀ (hcond₀ none) hreg₀
  let θ₀ : S ⊗[R] E₀ ≃ₐ[S] D₀ :=
    regularConductorAlgEquiv d none hinj₀ hcond₀ hreg hreg₀ hcoeffn
  let : Module.Finite R E₀ :=
    finite_regularConductorSubalgebra d none hinj₀ hcond₀ hreg hreg₀
  obtain ⟨m, hm⟩ := exists_pow_map_inf_conductorTorsion_eq_bot
    (algebraMap R S (d none)) hinj hregS (I.map (algebraMap R S)) n
      (by simpa only [Ideal.map_pow] using hcond)
  let K : Ideal D := ((I.map (algebraMap R S)) ^ m).map (algebraMap S D)
  have hTK : T ⊓ K = ⊥ := by
    change conductorTorsionIdeal (D := D) (algebraMap R S (d none)) ⊓
      ((I.map (algebraMap R S)) ^ m).map (algebraMap S D) = ⊥
    rw [inf_comm]
    exact hm
  let Q := D ⧸ K
  let H := D ⧸ (T ⊔ K)
  let q₀ : D₀ →ₐ[S] H := Ideal.Quotient.factorₐ S (show T ≤ T ⊔ K from le_sup_left)
  let q₁ : Q →ₐ[S] H := Ideal.Quotient.factorₐ S (show K ≤ T ⊔ K from le_sup_right)
  have hQ : (I ^ m).map (algebraMap R S) • (⊤ : Submodule S Q) = ⊥ := by
    apply quotient_smul_top_eq_bot
    rw [Ideal.map_pow]
  have hH : (I ^ m).map (algebraMap R S) • (⊤ : Submodule S H) = ⊥ := by
    apply quotient_smul_top_eq_bot
    rw [Ideal.map_pow]
    exact le_sup_right
  let : Module.Finite R Q := finite_restrictScalars (I ^ m) (hcoeff m) hQ
  let θQ : S ⊗[R] Q ≃ₐ[S] Q := torsionTensorAlgEquiv (I ^ m) (hcoeff m) hQ
  let θH : S ⊗[R] H ≃ₐ[S] H := torsionTensorAlgEquiv (I ^ m) (hcoeff m) hH
  let F : E₀ →ₐ[R] H := (q₀.restrictScalars R).comp ψ₀
  let G : Q →ₐ[R] H := q₁.restrictScalars R
  let E := compatiblePairAlgebra F G
  let : Module.Finite R E := finite_compatiblePairAlgebra F G
  have hF (z : S ⊗[R] E₀) :
      θH (Algebra.TensorProduct.map (AlgHom.id S S) F z) = q₀ (θ₀ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul s e =>
        change torsionTensorAlgEquiv (I ^ m) (hcoeff m) hH (s ⊗ₜ[R] F e) =
          q₀ (regularConductorAlgEquiv d none hinj₀ hcond₀ hreg hreg₀ hcoeffn
            (s ⊗ₜ[R] e))
        rw [torsionTensorAlgEquiv_tmul, regularConductorAlgEquiv_tmul]
        change algebraMap S H s * q₀ (ψ₀ e) = q₀ (algebraMap S D₀ s * ψ₀ e)
        rw [map_mul, q₀.commutes]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have hG (z : S ⊗[R] Q) :
      θH (Algebra.TensorProduct.map (AlgHom.id S S) G z) = q₁ (θQ z) := by
    induction z using TensorProduct.inductionOn with
    | tmul s e =>
        change torsionTensorAlgEquiv (I ^ m) (hcoeff m) hH (s ⊗ₜ[R] q₁ e) =
          q₁ (torsionTensorAlgEquiv (I ^ m) (hcoeff m) hQ (s ⊗ₜ[R] e))
        rw [torsionTensorAlgEquiv_tmul, torsionTensorAlgEquiv_tmul, map_mul, q₁.commutes]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  let θpair : S ⊗[R] E ≃ₐ[S] quotientFibreProduct (S := S) T K :=
    (tensorCompatiblePairEquiv F G).trans
      (equalizerTransport (AlgEquiv.prodCongr θ₀ θQ) θH _ _ _ _
        (fun z => hF z.1) (fun z => hG z.2))
  let θ : S ⊗[R] E ≃ₐ[S] D :=
    θpair.trans (quotientFibreProductEquiv T K hTK).symm
  refine ⟨E, inferInstance, inferInstance, inferInstance, θ, ?_, ?_⟩
  · intro s
    exact θ.commutes s
  · intro f hf
    apply compatiblePair_localizationBaseMap_bijective F G
      (regularConductorSubalgebra_algebraMap_injective d none hinj₀ hcond₀ hreg) f n m
    · intro e
      apply regularConductorSubalgebra_conductor d none hinj₀ hcond₀ hreg hreg₀ (f ^ n)
      rw [hspan]
      exact Ideal.pow_mem_pow hf n
    · intro q
      exact source_smul_eq_zero_of_extended_annihilation (I ^ m) hQ
        (f ^ m) (Ideal.pow_mem_pow hf m) q

end FiniteModel

section InputReductions

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A finite coefficient correction raises the error from `JS` to
`(JI)S`, retaining a correcting coefficient in the original source ideal. -/
theorem exists_coefficient_correction (I J : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap R S))).comp (algebraMap R S)))
    (x : S) (hx : x ∈ J.map (algebraMap R S)) :
    ∃ a ∈ J, x - algebraMap R S a ∈ (J * I).map (algebraMap R S) := by
  have hx' : x ∈ J • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  refine Submodule.smul_induction_on hx' (fun a ha s _ => ?_)
    (fun x y hx hy => ?_)
  · obtain ⟨b, hb⟩ := exists_sub_mem_extendedIdeal I hcoeff s
    refine ⟨a * b, J.mul_mem_right b ha, ?_⟩
    rw [Algebra.smul_def, map_mul, ← mul_sub, Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R S) ha) hb
  · obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a + b, J.add_mem ha hb, ?_⟩
    rw [map_add, add_sub_add_comm]
    exact ((J * I).map (algebraMap R S)).add_mem hxa hyb

/-- Surjectivity modulo the original extended ideal gives original
coefficients modulo every power. Flatness and finite generation are not needed. -/
theorem exists_sub_mem_extendedIdeal_pow (I : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap R S))).comp (algebraMap R S)))
    (m : ℕ) (s : S) :
    ∃ a : R, s - algebraMap R S a ∈ (I ^ m).map (algebraMap R S) := by
  induction m generalizing s with
  | zero =>
      refine ⟨0, ?_⟩
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Submodule.mem_top
  | succ m ih =>
      obtain ⟨a, ha⟩ := ih s
      obtain ⟨b, _, hb⟩ := exists_coefficient_correction I (I ^ m) hcoeff
        (s - algebraMap R S a) ha
      refine ⟨a + b, ?_⟩
      rw [pow_succ, map_add, sub_add_eq_sub_sub]
      exact hb

/-- Every finite-order quotient uses the same original scalar map. -/
theorem quotient_coefficients_surjective_pow (I : Ideal R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap R S))).comp (algebraMap R S))) (m : ℕ) :
    Function.Surjective
      ((Ideal.Quotient.mk ((I ^ m).map (algebraMap R S))).comp (algebraMap R S)) := by
  intro z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := exists_sub_mem_extendedIdeal_pow I hcoeff m s
  exact ⟨a, (Ideal.Quotient.eq.mpr ha).symm⟩

/-- The original zero-localization map is bijective, including the literal
`f=0` value occurring in the zero-ideal branch. -/
theorem localizationBaseMap_zero_bijective :
    Function.Bijective (localizationBaseMap (R := R) (S := S) 0) := by
  let : Subsingleton (Localization.Away (0 : R)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : R))
      (S := Localization.Away (0 : R)) (Submonoid.mem_powers (0 : R))
  let : Subsingleton (Localization.Away (algebraMap R S (0 : R))) :=
    IsLocalization.subsingleton (M := Submonoid.powers (algebraMap R S (0 : R)))
      (S := Localization.Away (algebraMap R S (0 : R))) (by
      rw [map_zero]
      exact Submonoid.mem_powers (0 : S))
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun z => ⟨0, Subsingleton.elim _ z⟩⟩

variable {D : Type*} [CommRing D] [Algebra S D]

/-- A power-annihilated actual kernel vanishes when the original ideal
contains a nonzero source-domain element and scalar extension is flat. -/
theorem algebraMap_injective_of_kernel_pow_annihilated [IsDomain R] [Module.Flat R S]
    (I : Ideal R) (a : R) (ha : a ∈ I) (ha0 : a ≠ 0) (u : ℕ)
    (hK : (I.map (algebraMap R S)) ^ u • (Algebra.linearMap S D).ker = ⊥) :
    Function.Injective (algebraMap S D) := by
  have hregR : IsSMulRegular R (a ^ u) := by
    intro x y hxy
    apply mul_left_cancel₀ (pow_ne_zero u ha0)
    exact hxy
  have hregS : IsSMulRegular S (algebraMap R S (a ^ u)) := hregR.of_flat
  intro x y hxy
  have hker : x - y ∈ (Algebra.linearMap S D).ker := by
    change algebraMap S D (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hmem : algebraMap R S (a ^ u) ∈ (I.map (algebraMap R S)) ^ u := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (algebraMap R S) (Ideal.pow_mem_pow ha u)
  have hz := Submodule.smul_mem_smul hmem hker
  rw [hK] at hz
  apply sub_eq_zero.mp
  apply hregS
  simpa only [smul_zero] using
    (show algebraMap R S (a ^ u) • (x - y) = 0 from hz)

/-- The literal cokernel quotient bound gives the original conductor
coefficients through the kernel of its actual quotient map. -/
theorem conductor_of_cokernel_pow_annihilated (I : Ideal R) (v : ℕ)
    (hM : (I.map (algebraMap R S)) ^ v •
      (⊤ : Submodule S (D ⧸ (Algebra.linearMap S D).range)) = ⊥) :
    ∀ s ∈ (I ^ v).map (algebraMap R S), ∀ z : D,
      ∃ a : S, algebraMap S D a = s • z := by
  intro s hs z
  let L := (Algebra.linearMap S D).range
  have hs' : s ∈ (I.map (algebraMap R S)) ^ v := by
    rw [← Ideal.map_pow]
    exact hs
  have hz := Submodule.smul_mem_smul hs'
    (Submodule.mem_top : L.mkQ z ∈ (⊤ : Submodule S (D ⧸ L)))
  rw [hM] at hz
  have hzero : L.mkQ (s • z) = 0 :=
    (L.mkQ.map_smul s z).trans (show s • L.mkQ z = 0 from hz)
  rw [Submodule.mkQ_apply] at hzero
  have hmem : s • z ∈ L := (Submodule.Quotient.mk_eq_zero L).mp hzero
  exact hmem

end InputReductions

section OriginalInput

universe u

variable {R S D : Type u} [CommRing R] [CommRing S] [CommRing D]
  [Algebra R S] [Algebra R D] [Algebra S D] [IsScalarTower R S D]
  [IsDomain R] [IsNoetherianRing R] [IsNoetherianRing S]
  [Module.FaithfullyFlat R S] [Module.Finite S D]

/-- Finite-modification algebra effectivity under the reviewed original
inputs. The displayed quotient equivalence is required to be the canonical
one on every original coefficient. The kernel and cokernel are the actual
ones of the original structural map. No conductor, model, or all-power
coefficient hypothesis is added. The case `I=0` uses the original counit. -/
theorem exists_finite_model (I : Ideal R)
    (e : R ⧸ I ≃+* S ⧸ I.map (algebraMap R S))
    (he : ∀ r : R, e (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r))
    (k n : ℕ)
    (hK : (I.map (algebraMap R S)) ^ k • (Algebra.linearMap S D).ker = ⊥)
    (hM : (I.map (algebraMap R S)) ^ n •
      (⊤ : Submodule S (D ⧸ (Algebra.linearMap S D).range)) = ⊥) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E), Module.Finite R E ∧
      ∃ θ : S ⊗[R] E ≃ₐ[S] D,
        (∀ s : S, θ (s ⊗ₜ[R] (1 : E)) = algebraMap S D s) ∧
        ∀ f ∈ I, Function.Bijective (localizationBaseMap (S := E) f) := by
  have hcoeff := quotient_coefficients_surjective I e he
  by_cases hI : I = ⊥
  · subst I
    have hD : (⊥ : Ideal R).map (algebraMap R S) • (⊤ : Submodule S D) = ⊥ := by
      simp
    let : Module.Finite R D := finite_restrictScalars (⊥ : Ideal R) hcoeff hD
    let θ : S ⊗[R] D ≃ₐ[S] D := torsionTensorAlgEquiv (⊥ : Ideal R) hcoeff hD
    refine ⟨D, inferInstance, inferInstance, inferInstance, θ, ?_, ?_⟩
    · intro s
      exact θ.commutes s
    · intro f hf
      have hf0 : f = 0 := hf
      subst f
      exact localizationBaseMap_zero_bijective
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hinj : Function.Injective (algebraMap S D) :=
      algebraMap_injective_of_kernel_pow_annihilated I a ha ha0 k hK
    have hreg : IsSMulRegular R (a ^ (n + 1)) := by
      intro x y hxy
      apply mul_left_cancel₀ (pow_ne_zero (n + 1) ha0)
      exact hxy
    apply exists_finite_model_of_regular_conductor I (n + 1) (a ^ (n + 1))
      (Ideal.pow_mem_pow ha (n + 1)) hreg hinj
    · intro s hs z
      apply conductor_of_cokernel_pow_annihilated I n hM s _ z
      exact Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) hs
    · exact quotient_coefficients_surjective_pow I hcoeff

end OriginalInput

end Algebra.Descent.FormalGluing
