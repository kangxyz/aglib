/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericHigherClassEffacementConsumer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.NormalModelClassZeroSpreading

/-! # Original higher classes on a finite normal coefficient model

The finite separable generic stage is produced internally. Its literal integral
closure is finite over the original normal Noetherian coefficient base, and
fraction continuity produces a nonempty principal open where the original
class vanishes. No generic-zero certificate is an input. This open need not
contain a prescribed point and does not supply whole-fibre local vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- A positive higher class on the original family becomes zero on a nonempty
principal open after a produced finite normal coefficient-base extension.
The original source Ext world is retained independently. -/
theorem exists_generic_higher_normal_principalOpen_zero
    (B L : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] [Field L] [Algebra B L] [IsFractionRing B L]
    {Y : Scheme.{u}} (e : Y ⟶ Spec (.of B)) [QuasiCompact e] [QuasiSeparated e]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    [IsAffine (pullback e (Spec.algebraMap B L))]
    [SmoothOfRelativeDimension 1 (pullback.snd e (Spec.algebraMap B L))]
    [GeometricallyConnected (pullback.snd e (Spec.algebraMap B L))]
    (M : AbelianSheaf.{u, u + 1} (Spec (.of B)))
    (n : ℕ) (hn : 0 < n) (hM : n • 𝟙 M = 0) (hunit : IsUnit (n : B))
    (q : ℕ) (hq : 2 ≤ q) (c : Sheaf.H.{eX} ((inverseImage e).obj M) q) :
    ∃ (K : FiniteGaloisIntermediateField L (SeparableClosure L))
      (E : Type u) (_ : Field E) (_ : Algebra K E),
      letI : Algebra L E := ((algebraMap K E).comp (algebraMap L K)).toAlgebra
      letI : Algebra B E := ((algebraMap L E).comp (algebraMap B L)).toAlgebra
      NormalPrincipalOpenClassZero B E e ((inverseImage e).obj M) q c := by
  apply generic_finiteEtaleField_killing_higher_class_induction
    B L e M n hn hM hunit q hq c
  intro K E hE hKE hfin hsep _ hc
  let : Field E := hE
  let : Algebra K E := hKE
  let : Algebra L E := ((algebraMap K E).comp (algebraMap L K)).toAlgebra
  let : IsScalarTower L K E := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra B E := ((algebraMap L E).comp (algebraMap B L)).toAlgebra
  let : IsScalarTower B L E := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite K E := hfin
  let : Algebra.IsSeparable K E := hsep
  let : Module.Finite L E := Module.Finite.trans K E
  let : Algebra.IsSeparable L E := Algebra.IsSeparable.trans L K E
  let e₀ := pullback.snd e (Spec.algebraMap B L)
  let e₁ := pullback.snd e₀ (Spec.algebraMap L K)
  let a := pullback.fst e₁ (Spec.algebraMap K E) ≫
    (pullback.fst e₀ (Spec.algebraMap L K) ≫ pullback.fst e (Spec.algebraMap B L))
  let b := pullback.snd e₁ (Spec.algebraMap K E)
  have H : IsPullback a b e (Spec.algebraMap B E) := by
    have H₀ := (IsPullback.of_hasPullback e₁ (Spec.algebraMap K E)).paste_horiz
      ((IsPullback.of_hasPullback e₀ (Spec.algebraMap L K)).paste_horiz
        (IsPullback.of_hasPullback e (Spec.algebraMap B L)))
    have ht : Spec.algebraMap K E ≫
        (Spec.algebraMap L K ≫ Spec.algebraMap B L) = Spec.algebraMap B E := by
      simp only [Spec.algebraMap, ← Spec.map_comp]
      rfl
    simpa only [ht] using H₀
  refine ⟨K, E, hE, hKE, ?_⟩
  exact normal_principalOpen_class_zero_of_generic_zero
    B L E e a b H ((inverseImage e).obj M) q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
