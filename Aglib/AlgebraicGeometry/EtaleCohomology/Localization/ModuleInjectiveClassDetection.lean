/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleInjectiveCohomologyDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.OpenSummandDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedSummandDetection

/-! # Conditional two-branch detection of original injective coefficient classes

This is only the thin assembly of the original retract detector and the two
original summand-zero lemmas. Ordinary open exchange, lower-degree vanishing,
open restriction zero and closed transformed-class zero remain explicit
inputs. No geometric effacement or dimension induction is supplied here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eT eV eW dT dV dA

attribute [local instance] hasSheafifyLarge

variable {X U Z T V W : Scheme.{u}}
  [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
  [HasExt.{eW} (AbelianSheaf.{u, u + 1} W)]
  [HasDerivedCategory.{dT} (AbelianSheaf.{u, u + 1} T)]
  [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- The original injective presentation and original two coefficient arrows
kill the same class under the explicitly stated intermediate hypotheses.
The closed input is the transformed class after `a`, not raw restriction zero. -/
theorem exists_moduleInjective_class_detection
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I] :
    ∃ J : ModuleSheaf Z Λ, Injective J ∧
      ∃ a : (moduleInverseImage i Λ).obj I ⟶ J, Mono a ∧
        ∀ (b : T ⟶ X) (j' : V ⟶ T) (bU : V ⟶ U)
          (hj : j' ≫ b = bU ≫ j) (i' : W ⟶ T) (bZ : W ⟶ Z)
          (hi : IsPullback bZ i' i b),
          IsIso ((baseChangeMap j j' b bU hj).app
            ((SheafOfModules.toSheaf (constantRing U Λ)).obj
              ((moduleInverseImage j Λ).obj I))) →
          ∀ (q : ℕ), 0 < q →
            (∀ r : ℕ, 1 ≤ r → r < q →
              IsZero ((higherDirectImage j' r).obj ((inverseImage bU).obj
                ((SheafOfModules.toSheaf (constantRing U Λ)).obj
                  ((moduleInverseImage j Λ).obj I))))) →
            ∀ x : Sheaf.H.{eT} ((inverseImage b).obj
              ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q,
              cohomologyPullback j' _ q x = 0 →
              Sheaf.H.map
                (moduleClosedPullbackCoefficientMap i i' b bZ hi.w.symm Λ I J a) q
                (cohomologyPullback i' _ q x) = 0 →
              x = 0 := by
  obtain ⟨J, hJ, a, ha, hdetect⟩ :=
    exists_moduleInjective_open_closed_cohomology_detection j i hcomp Λ I
  refine ⟨J, hJ, a, ha, ?_⟩
  intro b j' bU hj i' bZ hi hβ q hq hvan x hopen hclosed
  let : IsIso ((baseChangeMap j j' b bU hj).app
      ((SheafOfModules.toSheaf (constantRing U Λ)).obj
        ((moduleInverseImage j Λ).obj I))) := hβ
  have ho := moduleOpenSummand_eq_zero_of_restriction j j' b bU hj Λ I q hq hvan x hopen
  have hc := moduleClosedSummand_eq_zero i i' b bZ hi Λ I J a q x hclosed
  exact hdetect b q x ho hc

end AlgebraicGeometry.Scheme.EtaleCohomology
