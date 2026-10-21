/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.SelectedRelationQuotient
public import Aglib.RingTheory.RegularLocalRing.Etale
public import Aglib.RingTheory.RegularLocalRing.Domain
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Domain local rings of the actual selected-equation chart

The source is the literal selected-equation Jacobian localization. Its local
rings are domains over a regular coefficient ring, via the actual etale
polynomial chart and the canonical map of prime localizations.
-/

@[expose] public noncomputable section

universe u v w t z

namespace Algebra.Presentation

variable {R : Type u} {B : Type v} {ι : Type w} {σ : Type t} {τ : Type z}
variable [CommRing R] [IsRegularRing R] [CommRing B] [Algebra R B]
variable [Finite ι] [Finite τ]
variable (P : Presentation R B ι σ) (e : τ → σ) (a : τ → ι)
variable (ha : Function.Injective a)

/-- The actual source local ring is a domain, without assuming regularity,
reducedness or irreducibility of the intermediate selected-equation quotient. -/
theorem selectedJacobianSource_local_isDomain
    (q : Ideal (P.SelectedJacobianSource e a ha)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) := by
  let n := Nat.card ι - Nat.card τ
  let T := MvPolynomial (Fin n) R
  let : IsStandardSmoothOfRelativeDimension n R (P.SelectedJacobianSource e a ha) :=
    P.selectedJacobianSource_isStandardSmoothOfRelativeDimension e a ha
  obtain ⟨g, hg⟩ :=
    IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R
      (P.SelectedJacobianSource e a ha)
  let : Algebra T (P.SelectedJacobianSource e a ha) := g.toRingHom.toAlgebra
  let : Algebra.Etale T (P.SelectedJacobianSource e a ha) := hg
  let : SMul T (P.SelectedJacobianSource e a ha) := Algebra.toSMul
  let : Module T (P.SelectedJacobianSource e a ha) := Algebra.toModule
  let : MulAction T (P.SelectedJacobianSource e a ha) :=
    Algebra.toModule.toDistribMulAction.toMulAction
  let : Algebra T (Localization.AtPrime q) := OreLocalization.instAlgebra
  let : IsScalarTower T (P.SelectedJacobianSource e a ha)
      (Localization.AtPrime q) := OreLocalization.instIsScalarTower
  let p : Ideal T := q.under T
  let : p.IsPrime := inferInstance
  let : q.LiesOver p := inferInstance
  let := Localization.AtPrime.algebraOfLiesOver p q
  let : IsScalarTower T (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
  let : IsNoetherianRing (P.SelectedJacobianSource e a ha) :=
    Algebra.FiniteType.isNoetherianRing T (P.SelectedJacobianSource e a ha)
  let : Algebra.EssFiniteType T (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp T (P.SelectedJacobianSource e a ha) (Localization.AtPrime q)
  let : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp T (Localization.AtPrime p) (Localization.AtPrime q)
  let : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars T
      (Localization.AtPrime p) (Localization.AtPrime q)
  let : IsLocalHom
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  let : IsRegularLocalRing (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.isRegularLocalRing_of_flat
      (Localization.AtPrime p) (Localization.AtPrime q)
  exact IsRegularLocalRing.isDomain_of_regularLocal (Localization.AtPrime q)

end Algebra.Presentation
