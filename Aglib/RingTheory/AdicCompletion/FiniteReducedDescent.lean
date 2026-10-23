/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteLocalization
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Reducedness descent through the actual completed finite algebra

The original finite injective map and the actual completed localizations
are retained. The residue algebra supplies the Artinian closed fiber and
the proved branch comparison; no normalization, normality, dimension, or
branch-decomposition premise is added.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open IsLocalRing

universe u

namespace AdicCompletion

private theorem reduced_of_algEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (hB : IsReduced B) :
    IsReduced A := by
  let : IsReduced B := hB
  exact isReduced_of_injective e e.injective

private theorem reduced_of_injective_algHom
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (hf : Function.Injective f) (hB : IsReduced B) : IsReduced A := by
  let : IsReduced B := hB
  exact isReduced_of_injective f hf

private theorem tensorIncludeLeft_injective
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Module.Flat R B]
    (hinj : Function.Injective (algebraMap R C)) :
    Function.Injective (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C) := by
  let : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hinj
  intro x y hxy
  apply Module.Flat.tensorProduct_mk_injective (R := R) (S := C) (M := B)
  apply (Algebra.TensorProduct.comm R C B).injective
  change x ⊗ₜ[R] (1 : C) = y ⊗ₜ[R] (1 : C) at hxy
  change (Algebra.TensorProduct.comm R C B) ((1 : C) ⊗ₜ[R] x) =
    (Algebra.TensorProduct.comm R C B) ((1 : C) ⊗ₜ[R] y)
  simpa only [Algebra.TensorProduct.comm_tmul] using hxy

/-- Reducedness of all actual completed maximal localizations of a
finite injective algebra descends to the original local base completion. -/
theorem isReduced_of_finite_of_completed_localizations
    (R C : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing C] [Algebra R C] [Module.Finite R C]
    (hinj : Function.Injective (algebraMap R C))
    (hred : ∀ (q : Ideal C) [q.IsMaximal],
      IsReduced (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  let B := AdicCompletion (maximalIdeal R) R
  let I : Ideal C := (maximalIdeal R).map (algebraMap R C)
  let : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let : Algebra (R ⧸ maximalIdeal R) (C ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (show maximalIdeal R ≤ I.comap (algebraMap R C) from Ideal.le_comap_map)
  let : IsScalarTower R (R ⧸ maximalIdeal R) (C ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite R (C ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap
      Ideal.Quotient.mk_surjective
  let : Module.Finite (R ⧸ maximalIdeal R) (C ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R) (C ⧸ I)
  let : IsArtinianRing (C ⧸ I) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  let J (q : MaximalSpectrum (C ⧸ I)) : Ideal C :=
    q.asIdeal.comap (Ideal.Quotient.mk I)
  let (q : MaximalSpectrum (C ⧸ I)) : (J q).IsMaximal := by
    let : q.asIdeal.IsMaximal := q.isMaximal
    exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let (q : MaximalSpectrum (C ⧸ I)) : IsReduced (AdicCompletion (J q) C) :=
    reduced_of_algEquiv
      (localizationAlgEquiv (J q) (Localization.AtPrime (J q))) (hred (J q))
  obtain ⟨e, _heval⟩ := exists_residueBranchesAlgEquiv I
  have hbranches : IsReduced
      (∀ q : MaximalSpectrum (C ⧸ I), AdicCompletion (J q) C) := inferInstance
  have hC : IsReduced (AdicCompletion I C) := reduced_of_algEquiv e hbranches
  have hTensor : IsReduced (B ⊗[R] C) :=
    reduced_of_algEquiv (tensorEquivExtendedCompletion (S := C) (maximalIdeal R)) hC
  exact reduced_of_injective_algHom
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C)
    (tensorIncludeLeft_injective R B C hinj) hTensor

end AdicCompletion
