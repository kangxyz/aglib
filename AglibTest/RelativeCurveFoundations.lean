/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.PositiveSectionIsomorphism
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FibreClass

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.LineBundleEvaluation
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Family
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Regular
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteFlat
public import Aglib.AlgebraicGeometry.Picard.Relative.Groups
public import Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism

/-!
# Relative curve foundation consumer checks

The original proper-flat cohomology base is locally Noetherian. The new test
scheme in its canonical base-change conclusion is arbitrary. Graph ideals,
zero schemes and the normalized class functor also keep arbitrary test schemes.
These checks use the actual native objects and canonical forward maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.Hom

universe u

section ArbitraryNewBase
variable {S X T : Scheme.{u}} [IsLocallyNoetherian S]
variable (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
variable (M : X.Modules) [M.IsLocallyFree] [M.IsFinitePresentation]
variable (r : ℕ) (h : Scheme.Cohomology.FibreCohomologyConcentrated f M r)

-- There is deliberately no Noetherian, reducedness or flatness condition on `T` or `g`.
example (g : T ⟶ S) : IsIso (moduleBaseChangeMap f g M) :=
  (Scheme.Cohomology.localFreeCohomologyBaseChange_of_isLocallyNoetherian f M r h).2 T g

example : SheafHasRank ((Scheme.Modules.pushforward f).obj M) r :=
  (Scheme.Cohomology.localFreeCohomologyBaseChange_of_isLocallyNoetherian f M r h).1
end ArbitraryNewBase

section ActualIdealAndGraphMaps
variable {S X T T' : Scheme.{u}} (p : X ⟶ S)
variable (t : T ⟶ S) (t' : T' ⟶ S) (s : T ⟶ X) (hs : s ≫ p = t)
variable (a : T' ⟶ T) (ha : a ≫ t = t')

example : IsPullback (familyMap p t t' a ha) (pullback.snd p t') (pullback.snd p t) a :=
  familyMap_isPullback p t t' a ha

example : IsPullback (graph p t' (a ≫ s) (by rw [Category.assoc, hs, ha])) a
    (familyMap p t t' a ha) (graph p t s hs) :=
  graph_isPullback p t t' s hs a ha

example [SmoothOfRelativeDimension 1 p] [IsSeparated p] :
    IsLocallyRankOne (pullback p t) (idealModule (graph p t s hs)) :=
  graphIdeal_isLocallyRankOne smoothRelativeDivisorIdeal p t s hs
end ActualIdealAndGraphMaps

section ActualZeroScheme
variable {S X : Scheme.{u}} (p : X ⟶ S) [Flat p] [LocallyOfFinitePresentation p]
variable (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

example (hφ : GeometricFibreRegular p L φ) : Mono φ ∧ Flat (zeroInclusion φ ≫ p) :=
  fibrewiseRegularLineBundle X S p L φ inferInstance inferInstance hφ
end ActualZeroScheme

section NativeNormalization
variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

example {T T' : Over S} (a : T' ⟶ T) :
    familyMap p T.hom T'.hom a.left (Over.w a) = (Scheme.RelativePicard.familyScheme p).map a :=
  Scheme.RelativePicard.Classes.familyMap_eq_familyScheme_map p a

example : Scheme.RelativePicard.Classes.normalizedClassFunctor p o ho =
    Scheme.RelativePicard.normalizedPicardFunctor p o ho ⋙ forget AddCommGrpCat := rfl

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Scheme.RelativePicard.Classes.normalizedClassFunctor p o ho ≅
      (Scheme.RelativePicard.fppfPicardSheaf p).obj ⋙ forget AddCommGrpCat :=
  Functor.isoWhiskerRight
    (Scheme.RelativePicard.normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho)
    (forget AddCommGrpCat)
end NativeNormalization

section FiniteFlatDirectImage
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

example : IsFiniteLocallyFree Y (pushforwardStructureSheaf f) :=
  finiteFlat_pushforwardStructureSheaf_isFiniteLocallyFree f
end FiniteFlatDirectImage
