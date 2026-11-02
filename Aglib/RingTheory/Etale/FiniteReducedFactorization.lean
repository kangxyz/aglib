/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # The separable part of a finite reduced algebra over a field -/

@[expose] public noncomputable section

namespace Algebra.FiniteReducedFactorization

universe u v w

variable (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A]
  [Module.Finite K A] [IsReduced A]

/-- The residue field of one of the finitely many components. -/
abbrev Component (i : MaximalSpectrum A) := A ⧸ i.asIdeal

instance componentField (i : MaximalSpectrum A) : Field (Component A i) :=
  Ideal.Quotient.field i.asIdeal

/-- The finite separable subfield in a component's actual residue field. -/
abbrev SeparableComponent (i : MaximalSpectrum A) := separableClosure K (Component A i)

instance separableComponentFinite (i : MaximalSpectrum A) :
    Module.Finite K (SeparableComponent K A i) := inferInstance

instance separableComponentEtale (i : MaximalSpectrum A) :
    Algebra.Etale K (SeparableComponent K A i) := by
  have : Algebra.FormallyEtale K (SeparableComponent K A i) :=
    Algebra.FormallyEtale.of_isSeparable K _
  have : Algebra.FinitePresentation K (SeparableComponent K A i) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- The product of the actual maximal separable subfields of the residue fields. -/
abbrev SeparablePart := ∀ i : MaximalSpectrum A, SeparableComponent K A i

instance separablePartFinite : Module.Finite K (SeparablePart K A) := by
  have : IsArtinianRing A := .of_finite K A
  infer_instance

instance separablePartEtale : Algebra.Etale K (SeparablePart K A) := by
  have : IsArtinianRing A := .of_finite K A
  infer_instance

/-- The canonical Artinian product decomposition, over the original field. -/
def componentEquiv : A ≃ₐ[K] ∀ i : MaximalSpectrum A, Component A i := by
  have : IsArtinianRing A := .of_finite K A
  exact (IsArtinianRing.equivPi A).restrictScalars K

/-- The original inclusion of the separable part into the finite reduced algebra. -/
def inclusion : SeparablePart K A →ₐ[K] A :=
  (componentEquiv K A).symm.toAlgHom.comp
    (AlgHom.pi fun i => (separableClosure K (Component A i)).val.comp
      (Pi.evalAlgHom K (fun j => SeparableComponent K A j) i))

@[simp]
theorem componentEquiv_inclusion (b : SeparablePart K A) (i : MaximalSpectrum A) :
    componentEquiv K A (inclusion K A b) i = (b i : Component A i) := by
  simp [inclusion]

theorem inclusion_injective : Function.Injective (inclusion K A) := by
  intro b c h
  funext i
  apply Subtype.ext
  simpa only [componentEquiv_inclusion] using congrArg (fun a => componentEquiv K A a i) h

/-- The actual inclusion is a finite ring homomorphism. -/
theorem inclusion_finite : (inclusion K A).toRingHom.Finite := by
  let : Algebra (SeparablePart K A) A := (inclusion K A).toRingHom.toAlgebra
  have : IsScalarTower K (SeparablePart K A) A :=
    IsScalarTower.of_algebraMap_eq' (inclusion K A).comp_algebraMap.symm
  exact Module.Finite.of_restrictScalars_finite K (SeparablePart K A) A

/-- Every element has a power of the exponential characteristic in the separable part.
This is the concrete radicial property, also for a disconnected algebra. -/
theorem exists_pow_mem_inclusion_range (x : A) :
    ∃ n : ℕ, x ^ (ringExpChar K) ^ n ∈ (inclusion K A).range := by
  classical
  have : IsArtinianRing A := .of_finite K A
  let : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let p := ringExpChar K
  have (i : MaximalSpectrum A) : ExpChar (SeparableComponent K A i) p :=
    expChar_of_injective_algebraMap (algebraMap K (SeparableComponent K A i)).injective p
  have (i : MaximalSpectrum A) :
      IsPurelyInseparable (SeparableComponent K A i) (Component A i) :=
    separableClosure.isPurelyInseparable K _
  choose n y hy using fun i : MaximalSpectrum A =>
    IsPurelyInseparable.pow_mem (SeparableComponent K A i) p (componentEquiv K A x i)
  let N := Finset.univ.sup n
  have hn (i : MaximalSpectrum A) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, (fun i => y i ^ p ^ (N - n i)), ?_⟩
  change inclusion K A (fun i => y i ^ p ^ (N - n i)) = x ^ (ringExpChar K) ^ N
  apply (componentEquiv K A).injective
  ext i
  rw [componentEquiv_inclusion]
  simp only [map_pow, Pi.pow_apply]
  change (algebraMap (SeparableComponent K A i) (Component A i) (y i)) ^
    p ^ (N - n i) = (componentEquiv K A x i) ^ p ^ N
  rw [hy i, ← pow_mul, ← pow_add, Nat.add_sub_of_le (hn i)]

/-- Restriction along the actual inclusion is injective on maps to any field. -/
theorem injective_comp_inclusion (L : Type w) [Field L] :
    Function.Injective (fun f : A →+* L => f.comp (inclusion K A).toRingHom) := by
  intro f g h
  ext x
  obtain ⟨n, b, hb⟩ := exists_pow_mem_inclusion_range K A x
  have he := RingHom.congr_fun h b
  change inclusion K A b = x ^ (ringExpChar K) ^ n at hb
  change f (inclusion K A b) = g (inclusion K A b) at he
  rw [hb, map_pow, map_pow] at he
  have : ExpChar L (ringExpChar K) :=
    expChar_of_injective_ringHom (f.comp (algebraMap K A)).injective _
  exact iterateFrobenius_inj L (ringExpChar K) n he

end Algebra.FiniteReducedFactorization
