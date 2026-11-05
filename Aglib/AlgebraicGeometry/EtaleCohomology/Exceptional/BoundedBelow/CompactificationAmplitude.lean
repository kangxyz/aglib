/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CohomologicalBound
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ProperFiniteDimension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Bounds
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.UpperBound

/-! # Finite upper amplitude of an actual compactified module image

The proper geometric bound is produced internally, and the original exact
extension-by-zero single comparison supplies the input layers. Finite
Postnikov propagation retains the original bounded-below objects and maps.
The coefficient ring need only have a positive annihilator; it need not be
finite, Noetherian, or invertible on the schemes. No constructibility is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients DerivedCategory.Plus

universe u wX wM wS

attribute [local instance] hasSheafifyLarge

/-- One genuine upper-amplitude bound works for every bounded native module
complex under the same actual compactification. The lower input bound is
used only to make the original Postnikov filtration finite. -/
theorem exists_moduleCompactification_upperAmplitude
    {X S : Scheme.{u}} [CompactSpace S] {f : X ⟶ S}
    (C : Hom.Compactification f) (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    ∃ d : ℕ, ∀ (K : DerivedCategory.Plus (ModuleSheaf X Λ)) (a b : ℤ),
      K.IsGE a → K.IsLE b →
        ((moduleDerivedDirectImage Λ C.p).obj
          ((moduleDerivedLowerShriek C.j Λ).obj K)).IsLE ((d : ℤ) + b) := by
  obtain ⟨d, hd, _⟩ := Vanishing.exists_universal_higherDirectImage_torsion_bound C.p
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} C.Xbar)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  have hsingle (M : ModuleSheaf C.Xbar Λ) :
      ((moduleDerivedDirectImage Λ C.p).obj
        ((singleFunctor (ModuleSheaf C.Xbar Λ) 0).obj M)).IsLE (d : ℤ) := by
    apply (moduleDirectImage C.p Λ).rightDerivedFunctorPlus_single_isLE_of_bound M d
    intro q hq
    exact isZero_moduleRightDerived_obj_of_underlying Λ C.p M q
      (hd _ (moduleIsTorsion_of_nsmul_one_eq_zero C.Xbar Λ N hN hΛ M) q hq)
  refine ⟨d, ?_⟩
  intro K a b ha hb
  let : K.IsGE a := ha
  let : K.IsLE b := hb
  let F := moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p
  let : ∀ n : ℤ, (shiftFunctor (DerivedCategory.Plus (ModuleSheaf X Λ)) n).Additive :=
    fun n => inferInstance
  let : ∀ n : ℤ, (shiftFunctor (DerivedCategory.Plus (ModuleSheaf C.Xbar Λ)) n).Additive :=
    fun n => inferInstance
  let : ∀ n : ℤ, (shiftFunctor (DerivedCategory.Plus (ModuleSheaf S Λ)) n).Additive :=
    fun n => inferInstance
  apply DerivedCategory.Plus.isLE_obj_of_homology_single_zero_bounds
    (C := ModuleSheaf X Λ) (D := DerivedCategory.Plus (ModuleSheaf S Λ))
    F (DerivedCategory.Plus.TStructure.t (C := ModuleSheaf S Λ)) K a b (d : ℤ)
  intro i _ _
  let M := (homologyFunctor (ModuleSheaf X Λ) i).obj K
  let e : F.obj ((singleFunctor (ModuleSheaf X Λ) 0).obj M) ≅
      (moduleDerivedDirectImage Λ C.p).obj
        ((singleFunctor (ModuleSheaf C.Xbar Λ) 0).obj
          ((moduleLowerShriek C.j Λ).obj M)) :=
    (moduleDerivedDirectImage Λ C.p).mapIso
    (((moduleLowerShriek C.j Λ).rightDerivedFunctorPlusSingleIso 0).app M)
  let : ((moduleDerivedDirectImage Λ C.p).obj
      ((singleFunctor (ModuleSheaf C.Xbar Λ) 0).obj
        ((moduleLowerShriek C.j Λ).obj M))).IsLE (d : ℤ) :=
    hsingle ((moduleLowerShriek C.j Λ).obj M)
  exact TStructure.t.isLE_of_iso e.symm _

end AlgebraicGeometry.Scheme.EtaleCohomology
