/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Quotient

/-! # Detecting a closed quotient after another quotient

If a coefficient's actual K-quotient is already killed by a closed embedding's
kernel, reducing the original closed-embedding unit modulo K is invertible.
This uses only the original quotient universal properties and epimorphic units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
  (K : Y.IdealSheafData) (G : Y.Modules)

/-- Factor the K-quotient unit through the actual closed quotient. -/
def closedQuotientToKilledQuotient
    (h : killedByIdealSheaf i.ker ((idealSheafQuotientFunctor Y K).obj G)) :
    (pushforward i).obj ((Scheme.Modules.pullback i).obj G) ⟶
      (idealSheafQuotientFunctor Y K).obj G :=
  (pushforward i).map ((Scheme.Modules.pullback i).map ((idealSheafQuotientUnit Y K).app G)) ≫
    (closedImmersionDescentIso i _ h).hom

@[reassoc (attr := simp)]
theorem unit_closedQuotientToKilledQuotient
    (h : killedByIdealSheaf i.ker ((idealSheafQuotientFunctor Y K).obj G)) :
    (pullbackPushforwardAdjunction i).unit.app G ≫
      closedQuotientToKilledQuotient i K G h = (idealSheafQuotientUnit Y K).app G := by
  dsimp only [closedQuotientToKilledQuotient]
  have hn : (pullbackPushforwardAdjunction i).unit.app G ≫
      (pushforward i).map ((Scheme.Modules.pullback i).map
        ((idealSheafQuotientUnit Y K).app G)) =
      (idealSheafQuotientUnit Y K).app G ≫
        (pullbackPushforwardAdjunction i).unit.app
          ((idealSheafQuotientFunctor Y K).obj G) :=
    ((pullbackPushforwardAdjunction i).unit.naturality _).symm
  rw [← Category.assoc, hn, Category.assoc]
  change (idealSheafQuotientUnit Y K).app G ≫
    (closedImmersionDescentIso i _ h).inv ≫
      (closedImmersionDescentIso i _ h).hom = _
  exact (congrArg (fun t => (idealSheafQuotientUnit Y K).app G ≫ t)
    (closedImmersionDescentIso i _ h).inv_hom_id).trans (Category.comp_id _)

/-- Reducing the actual closed quotient unit is an isomorphism when the
reduced coefficient is already annihilated by the embedding ideal. -/
theorem quotient_closedUnit_isIso
    (h : killedByIdealSheaf i.ker ((idealSheafQuotientFunctor Y K).obj G)) :
    IsIso ((idealSheafQuotientFunctor Y K).map
      ((pullbackPushforwardAdjunction i).unit.app G)) := by
  let q := idealSheafQuotientFunctor Y K
  let η := idealSheafQuotientUnit Y K
  let u := (pullbackPushforwardAdjunction i).unit.app G
  let d := closedQuotientToKilledQuotient i K G h
  let v := idealSheafQuotientDesc Y K d (idealSheafQuotient_killed Y K G)
  have hn : η.app G ≫ q.map u = u ≫ η.app _ := (η.naturality u).symm
  have hd : η.app ((pushforward i).obj ((Scheme.Modules.pullback i).obj G)) ≫ v = d :=
    idealSheafQuotientUnit_desc Y K d (idealSheafQuotient_killed Y K G)
  have hu : u ≫ d = η.app G := unit_closedQuotientToKilledQuotient i K G h
  have huv : q.map u ≫ v = 𝟙 _ := by
    apply (cancel_epi (η.app G)).mp
    calc
      η.app G ≫ (q.map u ≫ v) = (η.app G ≫ q.map u) ≫ v :=
        (Category.assoc _ _ _).symm
      _ = (u ≫ η.app _) ≫ v := congrArg (fun t => t ≫ v) hn
      _ = u ≫ d := by rw [Category.assoc, hd]
      _ = η.app G ≫ 𝟙 _ := hu.trans (Category.comp_id _).symm
  have hvu : v ≫ q.map u = 𝟙 _ := by
    apply (cancel_epi (η.app ((pushforward i).obj ((Scheme.Modules.pullback i).obj G)))).mp
    apply (cancel_epi u).mp
    calc
      u ≫ (η.app _ ≫ (v ≫ q.map u)) = (u ≫ (η.app _ ≫ v)) ≫ q.map u := by
        simp only [Category.assoc]
      _ = (u ≫ d) ≫ q.map u := by rw [hd]
      _ = η.app G ≫ q.map u := by rw [hu]
      _ = u ≫ η.app _ := hn
      _ = u ≫ (η.app _ ≫ 𝟙 _) := by rw [Category.comp_id]
  exact ⟨⟨v, huv, hvu⟩⟩

end AlgebraicGeometry.Scheme.Cohomology
