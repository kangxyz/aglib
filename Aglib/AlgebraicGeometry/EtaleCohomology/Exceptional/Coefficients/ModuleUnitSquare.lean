/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionCubeUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitUnderlyingMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.UnderlyingComposition

/-! The original module unit square reflected through the actual comparison cube. -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

set_option maxHeartbeats 650000 in
-- The independently checked cube and four legs leave a costly conversion of
-- the original abelian square at the final argument.
/-- The original unit transports commute with the original module inverse-image square. -/
abbrev moduleUnitInverseImageIso_square_reflected {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (n : ℕ) :=
  let Λ := ULift.{u + 1} (ZMod n)
  let c := AddCommGrpCat.of Λ
  let ha := inverseImageSquareIso_constant f f' g g' h c
  let hm := moduleInverseImageSquareIso_underlying_whole Λ f f' g g' h
  let hL := moduleUnitInverseImageIso_underlying_left f n
  let hL' := moduleUnitInverseImageIso_underlying_left f' n
  let hG := moduleUnitInverseImageIso_underlying_left g n
  let hH := moduleUnitInverseImageIso_underlying_left g' n
  Functor.comparisonCubeEquation_unit
    (K := inverseImage f) (K' := inverseImage f') (G' := inverseImage g) (H' := inverseImage g')
    (U' := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj c)
    (V' := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj c)
    (W' := (constantSheaf S'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj c)
    (T' := (constantSheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj c)
    (moduleInverseImageUnderlyingIso Λ f) (moduleInverseImageUnderlyingIso Λ f')
    (moduleInverseImageUnderlyingIso Λ g) (moduleInverseImageUnderlyingIso Λ g')
    (moduleInverseImageSquareIso Λ f f' g g' h) (inverseImageSquareIso f f' g g' h)
    hm (moduleUnit S Λ)
    (moduleUnitUnderlyingIso S Λ) (moduleUnitUnderlyingIso X Λ)
    (moduleUnitUnderlyingIso S' Λ) (moduleUnitUnderlyingIso X' Λ)
    (moduleUnitInverseImageIso f n).hom (moduleUnitInverseImageIso f' n).hom
    (moduleUnitInverseImageIso g n).hom (moduleUnitInverseImageIso g' n).hom
    ((inverseImageConstantIso f).hom.app c) ((inverseImageConstantIso f').hom.app c)
    ((inverseImageConstantIso g).hom.app c) ((inverseImageConstantIso g').hom.app c)
    hL hL' hG hH ha

end AlgebraicGeometry.Scheme.EtaleCohomology
