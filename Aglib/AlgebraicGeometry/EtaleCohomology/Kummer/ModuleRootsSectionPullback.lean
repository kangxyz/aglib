/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology

/-! Original roots cohomology and Ext pulled back along an actual section. -/

open CategoryTheory CategoryTheory.Abelian
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients

universe u wX wY aX aY

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable {X Y : Scheme.{u}} [ConnectedSpace X] (f : Y ⟶ X) (i : X ⟶ Y)
  (hi : i ≫ f = 𝟙 X) (n : ℕ) (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{aX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{aY} (AbelianSheaf.{u, u + 1} Y)]

include hi in
/-- Original roots cohomology restricts a pullback class along the original section. -/
theorem rootsCohomologyPullback_section (q : ℕ) (x : Sheaf.H.{aX} (mu X n) q) :
    rootsCohomologyPullback.{u, aY, aX} i n hn (levelInvertible f n hnX) q
      (rootsCohomologyPullback.{u, aX, aY} f n hn hnX q x) = x := by
  have h := rootsCohomologyPullback_comp.{u, aX, aY, aX} f i n hn hnX q x
  have h' := congrArg (fun f' : X ⟶ X => rootsCohomologyPullback.{u, aX, aX} f' n hn hnX q x) hi
  let a := cohomologyPullback (𝟙 X) (mu X n) q x
  have hz : rootsCohomologyPullback.{u, aX, aX} (𝟙 X) n hn hnX q x = x :=
    (congrArg (fun g => Sheaf.H.map g q a)
      (SectionPullback.rootsPullbackIso_identity X n hn hnX)).trans
        (cohomologyPullback_id X (mu X n) q x)
  exact h.symm.trans (h'.trans hz)

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable [HasExt.{wX} (ModuleSheaf X Λ)] [HasExt.{wY} (ModuleSheaf Y Λ)]

include hi in
/-- The same original section law for module unit Ext with the original roots target. -/
theorem moduleRootsUnitExtPullback_section (q : ℕ)
    (x : Ext.{wX} (moduleUnit X Λ) (moduleRootsOfUnity X n) q) :
    moduleRootsUnitExtPullback.{u, wY, wX} i n hn (levelInvertible f n hnX) q
      (moduleRootsUnitExtPullback.{u, wX, wY} f n hn hnX q x) = x := by
  let e := moduleRootsUnitExtCohomologyAddEquiv.{u, wX, aX} X n q
  let e' := moduleRootsUnitExtCohomologyAddEquiv.{u, wY, aY} Y n q
  let y := moduleRootsUnitExtPullback.{u, wX, wY} f n hn hnX q x
  have h₁ : e' y = rootsCohomologyPullback.{u, aX, aY} f n hn hnX q (e x) :=
    DFunLike.congr_fun (moduleRootsUnitExtCohomologyPullback_square.{u, wX, wY, aX, aY}
      f n hn hnX q) x
  have h₂ : e (moduleRootsUnitExtPullback.{u, wY, wX} i n hn (levelInvertible f n hnX) q y) =
      rootsCohomologyPullback.{u, aY, aX} i n hn (levelInvertible f n hnX) q (e' y) :=
    DFunLike.congr_fun (moduleRootsUnitExtCohomologyPullback_square.{u, wY, wX, aY, aX}
      i n hn (levelInvertible f n hnX) q) y
  apply e.injective
  exact h₂.trans ((congrArg (rootsCohomologyPullback i n hn (levelInvertible f n hnX) q) h₁).trans
    (rootsCohomologyPullback_section f i hi n hn hnX q (e x)))

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
