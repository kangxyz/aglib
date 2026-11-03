/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison

/-!
# The original degree-zero flat base-change square for canonical localization

The existing derived flat mate retains its whole complex-unit equation. The
native degree-zero normalization therefore identifies its homology comparison
with the original ordinary sheaf mate, rather than an arbitrary isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Use the same standard realization as the original flat-base-change provider. -/
local instance canonicalTraceBaseChangeDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [Flat j]

/-- The higher-image degree-zero map is the original ordinary base-change mate,
conjugated by the actual right-derived-zero identifications. -/
theorem canonicalTraceHigherBaseChange_zero (M : U.Modules) :
    (pullback j).map ((pushforward f).rightDerivedZeroIsoSelf.hom.app M) ≫
        (cartesianBaseChangeMap a b f j h).app M =
      (higherDirectImageFlatBaseChangeMap a b f j h 0).app M ≫
        (pushforward b).rightDerivedZeroIsoSelf.hom.app ((pullback a).obj M) := by
  let :=  flat_cartesian_baseChange a b f j h
  let F := pushforward f
  let B := pushforward b
  let G := pullback j
  let H := pullback a
  let α := cartesianBaseChangeMap a b f j h
  let β := derivedFlatBaseChangeMap a b f j h
  have hunit (K : CochainComplex.Plus U.Modules) :
      G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        β.app (DerivedCategory.Plus.Q.obj K) ≫
        B.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
      G.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map ((Functor.exchangeOnComplexes F B G H α).app K) ≫
        B.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K) := by
    let : IsIso G.rightDerivedFunctorPlusUnit :=
      G.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    have hG := G.rightDerivedFunctorPlusExactComparison.inv_hom_id_app
      (F.mapCochainComplexPlus.obj K)
    change G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
      G.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj K) = 𝟙 _ at hG
    have hH := H.rightDerivedFunctorPlusExactComparison.inv_hom_id_app K
    change H.rightDerivedFunctorPlusUnit.app K ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app K = 𝟙 _ at hH
    apply (cancel_epi (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K))).mp
    have ht := congrArg (fun z => z ≫
      B.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K))
        (derivedFlatBaseChangeMap_unit a b f j h K)
    simp only [Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] at ht
    rw [← Category.assoc (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K))
      (G.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj K)),
      hG, Category.id_comp]
    have hB := congrArg B.rightDerivedFunctorPlus.map hH
    rw [B.rightDerivedFunctorPlus.map_comp, B.rightDerivedFunctorPlus.map_id] at hB
    have hα : (Functor.exchangeOnComplexes F B G H α).app K =
        (NatTrans.mapCochainComplexPlus α).app K := by
      change (𝟙 _ ≫ (NatTrans.mapCochainComplexPlus α).app K ≫ 𝟙 _) = _
      erw [Category.id_comp, Category.comp_id]
    rw [hα]
    dsimp only [F, B, G, H, β, α] at ht hB ⊢
    erw [hB, Category.comp_id] at ht
    exact ht
  have heq : Functor.higherExchangeZero F B G H β M =
      (higherDirectImageFlatBaseChangeMap a b f j h 0).app M := by
    have he := (higherDirectImageFlatBaseChangeMap_app a b f j h 0 M).symm
    convert he using 1 <;> rfl
  exact Functor.higherExchangeZero_normalization_of_eq F B G H α β M _ heq hunit

/-- Flat qcqs base change is invertible on the actual ordinary mate at a
quasicoherent coefficient, by the proved degree-zero square. -/
theorem canonicalTraceOrdinaryBaseChange_isIso [QuasiCompact f] [QuasiSeparated f]
    (M : U.Modules) [M.IsQuasicoherent] :
    IsIso ((cartesianBaseChangeMap a b f j h).app M) := by
  let :=  higherDirectImageFlatBaseChangeMap_isIso_app a b f j h M 0
  have he := canonicalTraceHigherBaseChange_zero a b f j h M
  have hc : IsIso ((pullback j).map ((pushforward f).rightDerivedZeroIsoSelf.hom.app M) ≫
      (cartesianBaseChangeMap a b f j h).app M) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((pullback j).map ((pushforward f).rightDerivedZeroIsoSelf.hom.app M))
    ((cartesianBaseChangeMap a b f j h).app M)

end AlgebraicGeometry.Scheme.Modules
