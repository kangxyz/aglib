/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericCoefficientPresentationConsumer
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineEtaleHigherCoefficient


/-! # Actual generic higher-class effacement

For degree at least two the original class is represented internally by the
actual finite constant class, and the existing affine higher-degree field
producer kills that class at a finite separable coefficient-field stage.
The original coefficient arrow and pullback composition then kill the original
class. No presentation or zero certificate is an external input. No source
cover is needed: the source-side cover in a subsequent two-field application
is the identity (automorphism cardinality one), not a newly chosen cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX
open FiniteEtale.FieldLimit
attribute [local instance] hasSheafifyLarge HasExt.standard

variable (B L : Type u) [CommRing B] [Field L] [Algebra B L]
  {Y : Scheme.{u}} (e : Y ⟶ Spec (.of B)) [QuasiCompact e] [QuasiSeparated e]

local notation "γ" => Spec.algebraMap B L
local notation "f₀" => pullback.fst e γ
local notation "e₀" => pullback.snd e γ

/-- A produced finite Galois stage and a produced finite separable stage kill
an original higher class with coefficients from the coefficient base. Its
original Ext world remains independent of the standard field-stage worlds. -/
theorem exists_generic_finiteEtaleField_killing_higher_class
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    [IsAffine (pullback e γ)] [SmoothOfRelativeDimension 1 e₀]
    [GeometricallyConnected e₀]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of B)))
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) (hunit : IsUnit (n : B))
    (q : ℕ) (hq : 2 ≤ q) (c : Sheaf.H.{eX} ((inverseImage e).obj F) q) :
    ∃ (K : FiniteGaloisIntermediateField L (SeparableClosure L))
      (E : Type u) (_ : Field E) (_ : Algebra K E),
      Module.Finite K E ∧ Algebra.IsSeparable K E ∧ Etale (Spec.algebraMap K E) ∧
      cohomologyPullback.{u, eX, u + 2}
        (pullback.fst (pullback.snd e₀ (Spec.algebraMap L K)) (Spec.algebraMap K E) ≫
          (pullback.fst e₀ (Spec.algebraMap L K) ≫ f₀))
        ((inverseImage e).obj F) q c = 0 := by
  apply generic_finiteGalois_coefficient_presentation_induction.{u, eX, u + 2, u + 2}
    B L e F n hn hF q c
  intro K C hC hfin hCn d β hd
  let := hC
  let := hfin
  let f₁ := pullback.fst e₀ (Spec.algebraMap L K)
  let e₁ := pullback.snd e₀ (Spec.algebraMap L K)
  let : SmoothOfRelativeDimension 1 e₁ :=
    (@MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} _ (@SmoothOfRelativeDimension 1)
      (smoothOfRelativeDimension_isStableUnderBaseChange 1))
      (IsPullback.of_hasPullback e₀ (Spec.algebraMap L K)) inferInstance
  let : ConnectedSpace (pullback e₀ (Spec.algebraMap L K) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton e₁
  have hunitK : IsUnit (n : K) := by
    simpa only [map_natCast] using
      (hunit.map (algebraMap B L)).map (algebraMap L K)
  exact ⟨K, exists_affine_finiteEtaleField_killing_coefficient_higher
    K (pullback e₀ (Spec.algebraMap L K)) e₁
    (f₁ ≫ f₀) ((inverseImage e).obj F) C n hn hCn hunitK q hq c d β hd⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
