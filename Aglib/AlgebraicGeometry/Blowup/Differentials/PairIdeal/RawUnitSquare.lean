/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawRestriction
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawSource
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawTarget
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawUnitTarget
public import Aglib.AlgebraicGeometry.Blowup.Differentials.UnitMap
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient


/-!
# The actual local raw family satisfies the same global unit square

The original source triangle and original target/unit comparison give the
literal restriction of one global square. No overlap equality is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

private theorem square_of_functor_comparison {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (e : F ≅ G) {P M N : C} (b : P ⟶ M) (t : P ⟶ N)
    (r : F.obj M ⟶ F.obj N)
    (h : G.map b ≫ e.inv.app M ≫ r ≫ e.hom.app N = G.map t) :
    F.map b ≫ r = F.map t := by
  apply (cancel_mono (e.hom.app N)).mp
  calc
    _ = (F.map b ≫ e.hom.app M) ≫ e.inv.app M ≫ r ≫ e.hom.app N := by
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    _ = (e.hom.app P ≫ G.map b) ≫ e.inv.app M ≫ r ≫ e.hom.app N :=
      congrArg (fun z => z ≫ e.inv.app M ≫ r ≫ e.hom.app N) (e.hom.naturality b)
    _ = e.hom.app P ≫ G.map t := by rw [Category.assoc, h]
    _ = _ := (e.hom.naturality t).symm

private theorem square_of_functor_comparison_of_source_unit
    {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (e : F ≅ G) {P M N : C} (b : P ⟶ M) (t : P ⟶ N)
    {U V : D} (s : F.obj M ⟶ U) (q : U ⟶ G.obj N)
    (c : G.obj P ⟶ V) (a : V ⟶ U)
    (hs : G.map b ≫ e.inv.app M ≫ s = c ≫ a)
    (hu : c ≫ a ≫ q = G.map t) :
    F.map b ≫ ((s ≫ q) ≫ e.inv.app N) = F.map t := by
  apply square_of_functor_comparison F G e b t ((s ≫ q) ≫ e.inv.app N)
  calc
    _ = (G.map b ≫ e.inv.app M ≫ s) ≫ q := by
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    _ = (c ≫ a) ≫ q := congrArg (fun z => z ≫ q) hs
    _ = G.map t := by simpa only [Category.assoc] using hu

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "S" => Localization.Away.saturatedChart R I x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)

/-- The actual source/unit paste for the literal original raw-restriction components. -/
private theorem pairIdeal_rawRestrictionComponents_unit :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    let β := rawFormsPullback (Spec.map α) (blowdown I) n
    let e := Scheme.Modules.restrictFunctorIsoPullback f
    let src := pairIdealRawSourceIso Λ R I x y hI n
    let tgt := pairIdealOnePoleRawTargetMap Λ R K I x y hI hx hy n L φ
    let t := pairIdealOnePoleUnitMap Λ R I n L φ
    (Scheme.Modules.restrictFunctor f).map β ≫
        ((src.hom ≫ tgt) ≫ e.inv.app (centreTwistedPullbackLine I L).val) =
      (Scheme.Modules.restrictFunctor f).map t := by
  intro f hf β e src tgt t
  have hs := pairIdealRawSourceIso_pullback Λ R I x y hI n
  have hu := pairIdealOnePoleRawTargetMap_unit Λ R K I x y hI hx hy n L φ
  dsimp only [Functor.comp_obj] at hs hu
  have hp := square_of_functor_comparison_of_source_unit
    (N := (centreTwistedPullbackLine I L).val)
    (Scheme.Modules.restrictFunctor f) (pullback f) e β t src.hom tgt
    ((pairIdealChartBasePullbackIso R I x y hI).hom.app _)
    (rawFormsPullback (Spec.map α)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) n)
    hs hu
  exact hp

/-- The actual local raw map satisfies the restriction of the original global unit square. -/
theorem pairIdealOnePoleRawRestrictionMap_unit :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y hI)
    let _ : IsOpenImmersion f := pairIdeal_chart_isOpenImmersion R I x y hI
    (Scheme.Modules.restrictFunctor f).map (rawFormsPullback (Spec.map α) (blowdown I) n) ≫
        pairIdealOnePoleRawRestrictionMap Λ R K I x y hI hx hy n L φ =
      (Scheme.Modules.restrictFunctor f).map (pairIdealOnePoleUnitMap Λ R I n L φ) := by
  intro f hf
  let β := rawFormsPullback (Spec.map α) (blowdown I) n
  have hp := pairIdeal_rawRestrictionComponents_unit Λ R K I x y hI hx hy n L φ
  have hr := pairIdealOnePoleRawRestrictionMap_eq Λ R K I x y hI hx hy n L φ
  exact (congrArg (fun z :
      (Scheme.Modules.restrictFunctor f).obj
          (moduleExteriorPower (canonicalBlowup I)
            (relativeDifferentialSheaf (blowdown I ≫ Spec.map α)) n) ⟶
        (Scheme.Modules.restrictFunctor f).obj (centreTwistedPullbackLine I L).val =>
      (Scheme.Modules.restrictFunctor f).map β ≫ z) hr).trans hp


end AlgebraicGeometry.Scheme.Blowup.PairIdeal
