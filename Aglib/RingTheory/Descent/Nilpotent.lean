/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.TensorProduct.PurelyInseparable
public import Aglib.RingTheory.Descent.Morphisms

/-!
# Canonical algebra descent from nilpotent overlap augmentations

The effective descent consumer is the reviewed FE-02 `AlgebraDescent.Datum`
on `FaithfullyFlatAlgebraDescent.lean` SHA256
3426f90de31fb5831c17c911468f6553022fed0c2fdb4a5651e119e21009d7ca.
The coaction below is constructed by formal étaleness; the counit and cocycle
are proved by uniqueness of nilpotent lifting.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.NilpotentDescent` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`cf6206f46c8ad123b4d352cd92c0e9ff970799e5a155e9a9eb8bb5474bc17e55`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section

open scoped _root_.TensorProduct

namespace Algebra.Descent.Nilpotent

open Algebra.Descent

universe u v w

section NilpotentComap

variable {A C : Type*} [CommRing A] [CommRing C]

theorem _root_.Ideal.isNilpotent_comap_of_injective (I : Ideal C) (f : A →+* C)
    (hf : Function.Injective f) (hI : IsNilpotent I) : IsNilpotent (I.comap f) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, le_bot_iff.mp ?_⟩
  have H := Ideal.le_comap_pow (f := f) (K := I) n
  rw [hn] at H
  exact H.trans (Ideal.comap_bot_le_of_injective f hf)

end NilpotentComap

section Datum

variable (R : Type u) (S : Type v) (B : Type w)
  [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

theorem counit_surjective : Function.Surjective (counit R S B) := by
  intro b
  exact ⟨1 ⊗ₜ[R] b, one_smul S b⟩

variable [Algebra.FormallyEtale S B]

/-- The unique coaction lifting the identity through the nilpotent counit. -/
def liftedCoaction (h : IsNilpotent (RingHom.ker (counit R S B).toRingHom)) :
    B →ₐ[S] S ⊗[R] B :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id S B) (counit R S B)
    (counit_surjective R S B) h

theorem counit_liftedCoaction (h : IsNilpotent (RingHom.ker (counit R S B).toRingHom)) :
    (counit R S B).comp (liftedCoaction R S B h) = AlgHom.id S B :=
  Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _

/-- Nilpotence of the first two counits is enough to construct the genuine
coassociative algebra descent datum; it is not a retained descent assumption. -/
def datumOfNilpotentCounits
    (h : IsNilpotent (RingHom.ker (counit R S B).toRingHom))
    (h₂ : IsNilpotent (RingHom.ker (counit R S (S ⊗[R] B)).toRingHom)) :
    Datum R S B where
  coaction := liftedCoaction R S B h
  counit_coaction := counit_liftedCoaction R S B h
  coassoc := by
    let ρ := liftedCoaction R S B h
    let μ := counit R S B
    let ν := counit R S (S ⊗[R] B)
    have hleft : ν.comp (Algebra.TensorProduct.map (AlgHom.id S S)
        (ρ.restrictScalars R)) = ρ.comp μ := by
      apply AlgHom.ext
      intro z
      induction z using _root_.TensorProduct.inductionOn with
      | tmul s b =>
        change s • ρ b = ρ (s • b)
        exact (map_smul ρ s b).symm
      | add x y hx hy => simp only [map_add, hx, hy]
    have hright : ν.comp (Algebra.TensorProduct.map (AlgHom.id S S)
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)) =
        AlgHom.id S (S ⊗[R] B) := by
      apply AlgHom.ext
      intro z
      induction z using _root_.TensorProduct.inductionOn with
      | tmul s b =>
        change s • (1 ⊗ₜ[R] b) = s ⊗ₜ[R] b
        simp only [_root_.TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => simp only [map_add, hx, hy]
    apply
      (Algebra.FormallyEtale.formallyEtale_comp_bijective ν (counit_surjective R S _) h₂).injective
    change ν.comp ((Algebra.TensorProduct.map (AlgHom.id S S)
      (ρ.restrictScalars R)).comp ρ) =
        ν.comp ((Algebra.TensorProduct.map (AlgHom.id S S)
          (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)).comp ρ)
    rw [← AlgHom.comp_assoc, hleft, AlgHom.comp_assoc,
      counit_liftedCoaction, AlgHom.comp_id, ← AlgHom.comp_assoc, hright, AlgHom.id_comp]

variable {B} {C : Type*} [CommRing C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
  [Algebra.FormallyEtale S C]

/-- All algebra maps respect the constructed nilpotent descent coactions. -/
def datumOfNilpotentCounitsHom
    (hB : IsNilpotent (RingHom.ker (counit R S B).toRingHom))
    (hB₂ : IsNilpotent (RingHom.ker (counit R S (S ⊗[R] B)).toRingHom))
    (hC : IsNilpotent (RingHom.ker (counit R S C).toRingHom))
    (hC₂ : IsNilpotent (RingHom.ker (counit R S (S ⊗[R] C)).toRingHom))
    (f : B →ₐ[S] C) :
    (datumOfNilpotentCounits R S B hB hB₂).Hom (datumOfNilpotentCounits R S C hC hC₂) where
  hom := f
  comm := by
    let μ := counit R S C
    have hmap : μ.comp (Algebra.TensorProduct.map (AlgHom.id S S)
        (f.restrictScalars R)) = f.comp (counit R S B) := by
      apply AlgHom.ext
      intro z
      induction z using _root_.TensorProduct.inductionOn with
      | tmul s b => exact (map_smul f s b).symm
      | add x y hx hy => simp only [map_add, hx, hy]
    apply
    (Algebra.FormallyEtale.formallyEtale_comp_bijective μ (counit_surjective R S C) hC).injective
    change μ.comp ((liftedCoaction R S C hC).comp f) = μ.comp
      ((Algebra.TensorProduct.map (AlgHom.id S S) (f.restrictScalars R)).comp
        (liftedCoaction R S B hB))
    rw [← AlgHom.comp_assoc, counit_liftedCoaction, AlgHom.id_comp,
      ← AlgHom.comp_assoc, hmap, AlgHom.comp_assoc, counit_liftedCoaction, AlgHom.comp_id]

end Datum

section FinitePureFields

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] [Module.Finite K L]
  (B : Type w) [CommRing B] [Algebra K B] [Algebra L B] [IsScalarTower K L B]

/-- The exact FE-02 counit has nilpotent kernel for a finite purely
inseparable field extension and any algebra over its target field. -/
theorem _root_.Algebra.Descent.PurelyInseparable.counit_ker_isNilpotent :
    IsNilpotent (RingHom.ker (counit K L B).toRingHom) := by
  let e := Algebra.TensorProduct.comm K L B
  have he : (Algebra.TensorProduct.tensorAugmentation K L B).toRingHom.comp e.toRingHom =
      (counit K L B).toRingHom := by
    apply RingHom.ext
    intro z
    induction z using _root_.TensorProduct.inductionOn with
    | tmul l b =>
      change b * algebraMap L B l = l • b
      rw [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← he, ← RingHom.comap_ker]
  exact Ideal.isNilpotent_comap_of_injective _ e.toRingHom e.injective
    (Algebra.TensorProduct.tensorAugmentation_ker_isNilpotent K L B)

/-- Every formally étale `L`-algebra obtains a canonical, proved descent datum
for a finite purely inseparable field extension `L/K`. -/
def _root_.Algebra.Descent.PurelyInseparable.finitePureDatum
    [Algebra.FormallyEtale L B] : Datum K L B :=
  datumOfNilpotentCounits K L B (Algebra.Descent.PurelyInseparable.counit_ker_isNilpotent K L B)
    (Algebra.Descent.PurelyInseparable.counit_ker_isNilpotent K L (L ⊗[K] B))

/-- The actual descended algebra and its reconstruction isomorphism. -/
def _root_.Algebra.Descent.PurelyInseparable.finitePureBaseChangeEquiv [Algebra.FormallyEtale L B] :
    L ⊗[K] (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).invariants ≃ₐ[L] B :=
  (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).baseChangeEquiv

theorem _root_.Algebra.Descent.PurelyInseparable.finitePure_invariants_finite
    [Algebra.FormallyEtale L B] [Module.Finite L B] :
    Module.Finite K (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).invariants :=
  (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).invariants_finite

theorem _root_.Algebra.Descent.PurelyInseparable.finitePure_invariants_etale [Algebra.Etale L B] :
    Algebra.Etale K (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).invariants :=
  (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).invariants_etale

variable {B} {C : Type*} [CommRing C] [Algebra K C] [Algebra L C] [IsScalarTower K L C]
  [Algebra.FormallyEtale L B] [Algebra.FormallyEtale L C]

/-- Every map between the original formally étale algebras respects the
constructed descent data. This follows from uniqueness of nilpotent lifts. -/
def _root_.Algebra.Descent.PurelyInseparable.finitePureDatumHom (f : B →ₐ[L] C) :
    (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).Hom
      (Algebra.Descent.PurelyInseparable.finitePureDatum K L C) where
  hom := f
  comm := by
    let μ := counit K L C
    let ρB := (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).coaction
    let ρC := (Algebra.Descent.PurelyInseparable.finitePureDatum K L C).coaction
    have hmap : μ.comp (Algebra.TensorProduct.map (AlgHom.id L L)
        (f.restrictScalars K)) = f.comp (counit K L B) := by
      apply AlgHom.ext
      intro z
      induction z using _root_.TensorProduct.inductionOn with
      | tmul l b => exact (map_smul f l b).symm
      | add x y hx hy => simp only [map_add, hx, hy]
    apply (Algebra.FormallyEtale.formallyEtale_comp_bijective μ (counit_surjective K L C)
      (Algebra.Descent.PurelyInseparable.counit_ker_isNilpotent K L C)).injective
    change μ.comp (ρC.comp f) = μ.comp
      ((Algebra.TensorProduct.map (AlgHom.id L L) (f.restrictScalars K)).comp ρB)
    rw [← AlgHom.comp_assoc,
      (Algebra.Descent.PurelyInseparable.finitePureDatum K L C).counit_coaction, AlgHom.id_comp,
      ← AlgHom.comp_assoc, hmap, AlgHom.comp_assoc,
      (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).counit_coaction, AlgHom.comp_id]

/-- The descended algebra map is literal restriction to the equalizer. -/
def _root_.Algebra.Descent.PurelyInseparable.finitePureInvariantsMap (f : B →ₐ[L] C) :
    (Algebra.Descent.PurelyInseparable.finitePureDatum K L B).invariants →ₐ[K]
      (Algebra.Descent.PurelyInseparable.finitePureDatum K L C).invariants :=
  (Algebra.Descent.PurelyInseparable.finitePureDatumHom K L f).invariantsMap

end FinitePureFields

end Algebra.Descent.Nilpotent
