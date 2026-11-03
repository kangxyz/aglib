/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorAffine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FormsFiniteType
public import Aglib.RingTheory.Kaehler.Exterior.Map
public import Mathlib.RingTheory.Ideal.Height


/-!
# The actual affine bidual line of top relative forms

The coefficient actions are fixed by the original affine chart map before
measuring generic rank. The actual affine sections comparison followed by the
original differential localization produces the generic map; it is not an
extra hypothesis. The supplied generic top degree is determined upstream by
the original ordinary basis over the same coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u


open KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- Actual generic differential rank gives invertibility of the actual affine
bidual, with both coefficient algebras fixed by the original chart map. -/
theorem affineBidualForms_isLocallyRankOne
    {X : Scheme.{u}} [IsLocallyNoetherian X] {Λ R : CommRingCat.{u}}
    [IsDomain R] [IsRegularRing R]
    (a : X ⟶ Spec Λ) [LocallyOfFiniteType a]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hd : ringKrullDim R ≤ 2) :
    letI : Algebra Λ R := (Spec.preimage (j ≫ a)).hom.toAlgebra
    letI : Algebra Λ K :=
      ((algebraMap R K).comp (Spec.preimage (j ≫ a)).hom).toAlgebra
    Module.finrank K (KaehlerDifferential Λ K) = n →
      Invertible.IsLocallyRankOne (Spec R)
        ((show X.Modules from Invertible.dualSheaf X (Invertible.dualSheaf X
          (moduleExteriorPower X (relativeDifferentialSheaf a) n))).restrict j) := by
  let : Algebra Λ R := (Spec.preimage (j ≫ a)).hom.toAlgebra
  let : Algebra Λ K :=
    ((algebraMap R K).comp (Spec.preimage (j ≫ a)).hom).toAlgebra
  let : IsScalarTower Λ R K := IsScalarTower.of_algebraMap_eq' rfl
  intro hrank
  let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
  have hM : affineLocallyFiniteType X M := rawForms_affineLocallyFiniteType a n
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  let e := rawFormsAffineSectionsEquiv a j n
  let f := (KaehlerDifferential.mapExterior Λ R K n).comp e.toLinearMap
  let : IsLocalizedModule (nonZeroDivisors R)
      (KaehlerDifferential.mapExterior Λ R K n) :=
    KaehlerDifferential.mapExterior_isLocalizedModule Λ R K (nonZeroDivisors R) n
  let : IsLocalizedModule (nonZeroDivisors R) f :=
    IsLocalizedModule.of_linearEquiv_right (nonZeroDivisors R)
      (KaehlerDifferential.mapExterior Λ R K n) e
  let : Module.Finite R (KaehlerDifferential Λ R) := finite_kaehler_of_locallyOfFiniteType a j
  let : IsLocalizedModule (nonZeroDivisors R) (KaehlerDifferential.map Λ Λ R K) :=
    KaehlerDifferential.isLocalizedModule_map (R := Λ) (S := R) (T := K)
      (nonZeroDivisors R)
  let : Module.Finite K (KaehlerDifferential Λ K) :=
    Module.Finite.of_isLocalizedModule (nonZeroDivisors R) (KaehlerDifferential.map Λ Λ R K)
  have htop : Module.finrank K (⋀[K]^n (KaehlerDifferential Λ K)) = 1 := by
    rw [exteriorPower.finrank_eq, hrank, Nat.choose_self]
  apply Invertible.affineRestrictionBidual_isLocallyRankOne j M hM f htop
  intro p
  let : p.asIdeal.IsPrime := p.2
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal]
  exact (ringKrullDim_le_iff_height_le 2).mp hd p.2

end AlgebraicGeometry.Scheme.Modules.Differentials
