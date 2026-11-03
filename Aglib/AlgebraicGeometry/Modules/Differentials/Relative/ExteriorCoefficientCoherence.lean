/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.CoefficientIdentity
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.CongruenceCoherence
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Pushforward.Composition
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.PushforwardIdentity
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Identity.Core
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Naturality
public import Aglib.CategoryTheory.Functor.OriginalComparisonIdentities


/-!
# Original raw coefficient congruence and identity

Raw coefficients respect the original structural differential comparisons.
Their exact identity normalization retains the native pushforward identity.
The same raw comparisons compose, and their actual double duals retain these
laws through the already existing internal-Hom construction.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u


open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Differentials

/-- A structural equality gives the original raw coefficient square. -/
theorem rawFormsCoefficient_congr {X Y T : Scheme.{u}} {a a' : X ⟶ T}
    (ha : a = a') (b : Y ⟶ X) (n : ℕ) :
    (moduleExteriorPowerFunctor X n).map (relativeDifferentialCongrIso a ha).hom ≫
      rawFormsCoefficient a' b n =
    rawFormsCoefficient a b n ≫ (pushforward b).map
      ((moduleExteriorPowerFunctor Y n).map
        (relativeDifferentialCongrIso (b ≫ a) (congrArg (fun f => b ≫ f) ha)).hom) := by
  cases ha
  rw [relativeDifferentialCongrIso_refl, relativeDifferentialCongrIso_refl]
  exact Functor.originalComparison_refl_square
    (moduleExteriorPowerFunctor X n) (moduleExteriorPowerFunctor Y n) (pushforward b)
    (relativeDifferentialSheaf a) (relativeDifferentialSheaf (b ≫ a))
    (rawFormsCoefficient a b n)

/-- Original exterior structural comparisons compose with their actual equalities. -/
theorem rawFormsCongr_trans {X T : Scheme.{u}} {a a' a'' : X ⟶ T}
    (h : a = a') (h' : a' = a'') (n : ℕ) :
    (moduleExteriorPowerFunctor X n).map (relativeDifferentialCongrIso a h).hom ≫
      (moduleExteriorPowerFunctor X n).map (relativeDifferentialCongrIso a' h').hom =
    (moduleExteriorPowerFunctor X n).map (relativeDifferentialCongrIso a (h.trans h')).hom := by
  exact Functor.originalComparison_trans (moduleExteriorPowerFunctor X n)
    (relativeDifferentialCongrIso a h) (relativeDifferentialCongrIso a' h')
    (relativeDifferentialCongrIso a (h.trans h'))
    (relativeDifferentialCongrIso_trans h h')

/-- The actual double-dual structural comparisons use the existing composition law. -/
theorem rawFormsBidualCongr_trans {X T : Scheme.{u}} {a a' a'' : X ⟶ T}
    (h : a = a') (h' : a' = a'') (n : ℕ) :
    doubleDualMap X
        ((moduleExteriorPowerFunctor X n).map (relativeDifferentialCongrIso a h).hom) ≫
      doubleDualMap X
        ((moduleExteriorPowerFunctor X n).map (relativeDifferentialCongrIso a' h').hom) =
    doubleDualMap X
      ((moduleExteriorPowerFunctor X n).map (relativeDifferentialCongrIso a (h.trans h')).hom) :=
  (doubleDualMap_comp _ _).symm.trans (congrArg (doubleDualMap X) (rawFormsCongr_trans h h' n))

/-- Reflexive structural comparison is the identity also on the original bidual. -/
theorem rawFormsBidualCongr_refl {X T : Scheme.{u}} (a : X ⟶ T) (n : ℕ) :
    doubleDualMap X
      ((moduleExteriorPowerFunctor X n).map (relativeDifferentialCongrIso a rfl).hom) =
        𝟙 (dualSheaf X (dualSheaf X (moduleExteriorPower X (relativeDifferentialSheaf a) n))) := by
  rw [relativeDifferentialCongrIso_refl]
  exact doubleDualMap_map_refl X (moduleExteriorPowerFunctor X n)
    (relativeDifferentialSheaf a)

/-- The original raw identity coefficient is the native pushforward identity inverse. -/
theorem rawFormsCoefficient_id {X T : Scheme.{u}} (a : X ⟶ T) (n : ℕ) :
    rawFormsCoefficient a (𝟙 X) n ≫ (pushforward (𝟙 X)).map
      ((moduleExteriorPowerFunctor X n).map
        (relativeDifferentialCongrIso ((𝟙 X) ≫ a) (Category.id_comp a)).hom) =
    (pushforwardId X).inv.app (moduleExteriorPower X (relativeDifferentialSheaf a) n) := by
  have he := exteriorCoefficientMap_postcomp (𝟙 X) (relativeDifferentialSheaf a)
    (relativeDifferentialSheaf ((𝟙 X) ≫ a)) (differentialCoefficient a (𝟙 X)) n
    (relativeDifferentialCongrIso ((𝟙 X) ≫ a) (Category.id_comp a)).hom
  exact he.trans
    ((congrArg (fun f => exteriorCoefficientMap (𝟙 X) f n) (differentialCoefficient_id a)).trans
      (exteriorCoefficientMap_id X (relativeDifferentialSheaf a) n))

/-- Composing with the original pushforward identity gives the actual identity map. -/
theorem rawFormsCoefficient_id_pushforward {X T : Scheme.{u}} (a : X ⟶ T) (n : ℕ) :
    rawFormsCoefficient a (𝟙 X) n ≫ (pushforward (𝟙 X)).map
      ((moduleExteriorPowerFunctor X n).map
        (relativeDifferentialCongrIso ((𝟙 X) ≫ a) (Category.id_comp a)).hom) ≫
      (pushforwardId X).hom.app (moduleExteriorPower X (relativeDifferentialSheaf a) n) =
        𝟙 _ := by
  exact Functor.originalComparison_identity_normalization (pushforward (𝟙 X))
    (pushforwardId X) (rawFormsCoefficient a (𝟙 X) n)
    ((moduleExteriorPowerFunctor X n).map
      (relativeDifferentialCongrIso ((𝟙 X) ≫ a) (Category.id_comp a)).hom)
    (rawFormsCoefficient_id a n)

end AlgebraicGeometry.Scheme.Modules.Differentials
