/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ConstructibleDescent
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Original affine finite-image constructibility from a split base change

The tensor-product pushout supplies the actual spectrum pullback square.
The original split quotient supplies the actual surjective closed immersion
and finite-etale composite. Constructibility descends along precisely the
given surjective spectrum map, not along a larger unlocalized base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

/-- A genuine surjective affine base change with a split nilpotent quotient
preserves constructibility of the original finite direct image. -/
theorem isConstructible_directImage_of_splitBase
    {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] [Module.Finite R A]
    (hC : Function.Surjective (PrimeSpectrum.comap (algebraMap R C)))
    {J : Type u} [Finite J] (q : C ⊗[R] A →ₐ[C] (J → C))
    (hq : Function.Surjective q) (n : ℕ) (hn : (RingHom.ker q.toRingHom) ^ n = ⊥)
    {F : AbelianSheaf.{u, u + 1} (Spec (.of A))}
    (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((directImage (Spec.algebraMap R A)).obj F) := by
  let f := Spec.algebraMap R A
  let f' := Spec.algebraMap C (C ⊗[R] A)
  let g := Spec.algebraMap R C
  let g' := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A →ₐ[R] C ⊗[R] A).toRingHom)
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have : Surjective g := ⟨hC⟩
  have h : IsPullback g' f' f g :=
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R C A)).flip
  let i := Spec.map (CommRingCat.ofHom q.toRingHom)
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ hq
  have : Surjective i :=
    Scheme.FiniteEtale.SplitThickening.specMap_surjective_of_ker_pow_eq_bot q.toRingHom hq n hn
  have ht : i ≫ f' = Spec.algebraMap C (J → C) :=
    Scheme.FiniteEtale.SplitThickening.spec_splitQuotient_triangle q
  have : IsFinite (i ≫ f') := by
    rw [ht]
    exact Scheme.FiniteEtale.SplitThickening.splitProduct_isFinite C J
  have : Etale (i ≫ f') := by
    rw [ht]
    exact Scheme.FiniteEtale.SplitThickening.splitProduct_etale C J
  exact isConstructible_directImage_of_surjective_splitThickening f f' g g' h i hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
