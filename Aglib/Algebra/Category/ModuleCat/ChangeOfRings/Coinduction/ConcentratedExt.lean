/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Ext
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Ext from concentrated native derived coinduction

Concentration is tested on the original ambient Ext groups. The comparison uses
only the installed derived restriction/coinduction adjunction and the native
homology-normalized single isomorphism. In particular no projectivity of the
quotient over the ambient ring is required.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w v a b
namespace ModuleCat
variable {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
  [HasExt.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]
  (M : ModuleCat.{u} R) (n : ℕ)

/-- Vanishing of original ambient Ext below `n` gives the actual lower bound. -/
theorem derivedCoextendScalarsPlus_isGE_of_ext
    (h : ∀ j : ℕ, j < n →
      Subsingleton (Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M j)) :
    ((coextendScalars σ).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsGE (n : ℤ) := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro i hi
  by_cases hi0 : i < 0
  · exact Functor.isZero_homology_rightDerivedFunctorPlus_of_isGE
      (coextendScalars σ) ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M)
      0 i hi0
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    let E := derivedCoextendScalarsPlusHomologyExtAddEquiv σ M (injectiveResolution M) j
    let := h j (by omega)
    exact ⟨fun x y => E.injective (Subsingleton.elim _ _)⟩

/-- Vanishing above `n` gives the actual upper bound. -/
theorem derivedCoextendScalarsPlus_isLE_of_ext
    (h : ∀ j : ℕ, n < j →
      Subsingleton (Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M j)) :
    ((coextendScalars σ).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLE (n : ℤ) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro i hi
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let E := derivedCoextendScalarsPlusHomologyExtAddEquiv σ M (injectiveResolution M) j
  let := h j (by omega)
  exact ⟨fun x y => E.injective (Subsingleton.elim _ _)⟩

/-- Concentrated derived coinduction computes Ext over the target ring in all
natural degrees, with its actual target-ring homology module as coefficient. -/
def concentratedCoextendScalarsExtAddEquiv
    [HasExt.{v} (ModuleCat.{u} S)]
    (h : ∀ j : ℕ, j ≠ n →
      Subsingleton (Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M j))
    (N : ModuleCat.{u} S) (k : ℕ) :
    Ext.{v} N
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
        ((coextendScalars σ).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M))) k ≃+
      Ext.{w} ((restrictScalars σ).obj N) M (k + n) := by
  let F := (restrictScalars σ).rightDerivedFunctorPlus
  let G := (coextendScalars σ).rightDerivedFunctorPlus
  let X := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} S) 0).obj N
  let Y := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M
  let K := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj (G.obj Y)
  letI := derivedCoextendScalarsPlus_isGE_of_ext σ M n (fun j hj => h j (by omega))
  letI := derivedCoextendScalarsPlus_isLE_of_ext σ M n (fun j hj => h j (by omega))
  let e : (G.obj Y)⟦((k + n : ℕ) : ℤ)⟧ ≅
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} S) 0).obj K)⟦(k : ℤ)⟧ :=
    (shiftFunctor _ ((k + n : ℕ) : ℤ)).mapIso
        (DerivedCategory.Plus.isoSingleHomology (G.obj Y) (n : ℤ)) ≪≫
      ((DerivedCategory.Plus.singleFunctors (ModuleCat.{u} S)).shiftIso
        ((k + n : ℕ) : ℤ) (-(k : ℤ)) (n : ℤ) (by omega)).app K ≪≫
      (((DerivedCategory.Plus.singleFunctors (ModuleCat.{u} S)).shiftIso
        (k : ℤ) (-(k : ℤ)) 0 (by omega)).app K).symm
  let adj := (restrictCoextendScalarsAdj σ).rightDerivedFunctorPlus
  exact (Ext.homPlusAddEquiv k).trans
    (((CategoryTheory.Linear.homCongr ℤ (Iso.refl X)
      (e.symm ≪≫ (G.commShiftIso ((k + n : ℕ) : ℤ)).symm.app Y)).toAddEquiv).trans
      ((adj.homAddEquiv X (Y⟦((k + n : ℕ) : ℤ)⟧)).symm.trans
        (((CategoryTheory.Linear.homCongr ℤ
          ((restrictScalars σ).rightDerivedFunctorPlusSingleIso 0 |>.app N)
          (Iso.refl _)).toAddEquiv).trans (Ext.homPlusAddEquiv (k + n)).symm)))

end ModuleCat
