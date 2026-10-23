/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite generation by adic coefficient lifting

A separated module over a precomplete ring is finite if its quotient modulo
the chosen ideal is finite. Only the coefficient ring is assumed precomplete.
The target module need not be complete or known to be finite in advance.
-/

@[expose] public section

namespace IsPrecomplete

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- A finite product of precomplete modules is precomplete. -/
theorem pi_of_finite {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, IsPrecomplete I (M i)] : IsPrecomplete I (∀ i, M i) := by
  classical
  let := Fintype.ofFinite ι
  apply AdicCompletion.of_surjective_iff.mp
  intro x
  choose m hm using fun i ↦
    AdicCompletion.of_surjective I (M i) (AdicCompletion.pi I M x i)
  refine ⟨m, (AdicCompletion.piEquivOfFintype I M).injective ?_⟩
  apply funext
  intro i
  simpa only [AdicCompletion.piEquivOfFintype_apply, AdicCompletion.pi,
    LinearMap.pi_apply, AdicCompletion.map_of, LinearMap.proj_apply] using hm i

end IsPrecomplete

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (I : Ideal R)

/-- Lift finitely many generators modulo an ideal by completeness of their
coefficients. Separatedness of the target is sufficient. -/
theorem finite_of_isPrecomplete_of_isHausdorff
    [IsPrecomplete I R] [IsHausdorff I M]
    [Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))] : Module.Finite R M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R
    (M ⧸ (I • ⊤ : Submodule R M))
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (I • ⊤ : Submodule R M).mkQ f (Submodule.mkQ_surjective _)
  let : IsPrecomplete I (Fin n → R) := IsPrecomplete.pi_of_finite I (fun _ ↦ R)
  exact Module.Finite.of_surjective g
    (surjective_of_mkQ_comp_surjective (I := I) (hg.symm ▸ hf))

/-- The same criterion with finite generation over the quotient coefficient
ring, retaining the original action of `R` on the target. -/
theorem finite_of_isPrecomplete_of_isHausdorff_quotient
    [IsPrecomplete I R] [IsHausdorff I M]
    [Module.Finite (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))] : Module.Finite R M := by
  let : Module.Finite R (M ⧸ (I • ⊤ : Submodule R M)) :=
    Module.Finite.trans (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))
  exact finite_of_isPrecomplete_of_isHausdorff I

/-- For a Noetherian target algebra, containment of the extended ideal in the
Jacobson radical supplies the separatedness needed for coefficient lifting.
No finiteness of the algebra over the base is assumed. -/
theorem finite_of_isPrecomplete_of_le_jacobson
    {B : Type*} [CommRing B] [Algebra R B] [IsNoetherianRing B]
    [IsPrecomplete I R]
    (hI : I.map (algebraMap R B) ≤ Ideal.jacobson (⊥ : Ideal B))
    [Module.Finite R (B ⧸ (I • ⊤ : Submodule R B))] : Module.Finite R B := by
  let : IsHausdorff (I.map (algebraMap R B)) B :=
    IsHausdorff.of_le_jacobson _ B hI
  let : IsHausdorff I B :=
    (IsHausdorff.map_algebraMap_iff (R := R) (S := B) (I := I) (M := B)).mp inferInstance
  exact finite_of_isPrecomplete_of_isHausdorff I

end Module
