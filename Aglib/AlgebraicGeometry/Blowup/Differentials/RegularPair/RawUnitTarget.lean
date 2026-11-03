/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawSource
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleRaw
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleRawSquare
public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.OnePoleTarget
public import Aglib.AlgebraicGeometry.Blowup.Differentials.UnitMap
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.ComposedCoefficient
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# The original local raw unit square has one intrinsic global right-hand side

Transport the proved original local square through the original base-line
and target comparisons. Both the coefficient and exceptional section retain
their original maps. This is not yet overlap gluing.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u vK


open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Blowup.PairIdeal
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.RegularPair

private theorem recover_target {C : Type*} [Category C] {A B D : C}
    (g : A ⟶ D) (e : B ≅ D) : (g ≫ e.inv) ≫ e.hom = g := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (x y : R)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "I" => Ideal.span (Set.insert x (Set.singleton y))
local notation "S" => Localization.Away.saturatedChart R I x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "σ" => CommRingCat.ofHom (algebraMap R S)
local notation "B" => Blowup.blowupDatum (Blowup.affineCenter R I)
local notation "M" => moduleExteriorPower (Spec (CommRingCat.of R))
  (relativeDifferentialSheaf (Spec.map α)) n
local notation "Q" => Subtype.val
  (Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original local raw map satisfies the intrinsic global coefficient/unit equation. -/
theorem saturatedPairOnePoleRawTargetMap_unit :
    let f : Spec (.of S) ⟶ canonicalBlowup I := chartMap B (firstGenerator I x y rfl)
    let e := saturatedPairChartBasePullbackIso R x y
    e.hom.app M ≫ rawFormsPullback (Spec.map α) (Spec.map σ) n ≫
        saturatedPairOnePoleRawTargetMap Λ R K x y hx hy n L φ =
      (pullback f).map (pairIdealOnePoleUnitMap Λ R I n L φ) := by
  intro f e
  let s : SheafOfModules.unit (canonicalBlowup I).ringCatSheaf ⟶ Q :=
    cartierDualIdealSection (centreι B)
  let P := Invertible.pullbackLineBundle (blowdown I) L
  let N := Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I)
  let U := Invertible.pullbackLineBundle (Spec.map σ) L
  let t : (pullback f).obj (Invertible.tensorLineBundle (canonicalBlowup I) P N).val ≅
      (Invertible.tensorLineBundle (Spec (.of S)) U
        (Invertible.pullbackLineBundle f N)).val := saturatedPairOnePoleTargetIso R x y L
  have hr : saturatedPairOnePoleRawTargetMap Λ R K x y hx hy n L φ ≫ t.hom =
      saturatedPairOnePoleRawMap Λ R K x y hx hy n L φ :=
    recover_target (saturatedPairOnePoleRawMap Λ R K x y hx hy n L φ) t
  have hp := positiveSection_composedCoefficient_transport f (blowdown I) (Spec.map σ)
    (pairIdeal_chartBase_triangle R I x y rfl) L N M φ s
  have ht := saturatedPairOnePoleTargetIso_hom R x y L
  have hn := e.hom.naturality φ
  have hu := saturatedPairOnePoleRawMap_unit Λ R K x y hx hy n L φ
  apply (Iso.cancel_iso_hom_right _ _ t).mp
  simp only [Category.assoc, hr]
  have hp' : (pullback f).map (pairIdealOnePoleUnitMap Λ R I n L φ) ≫ t.hom =
      (pullback f).map ((pullback (blowdown I)).map φ) ≫ e.hom.app L.val ≫
        (positiveCartierTensorSection (Spec (.of S)) ((pullback f).obj Q)
          ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app
            ((pullback (Spec.map σ)).obj L.val) ≫
        (tensorSheafBraiding (Spec (.of S)) ((pullback f).obj Q)
          ((pullback (Spec.map σ)).obj L.val)).hom := by
    have hcongr := congrArg (fun z =>
      (pullback f).map (pairIdealOnePoleUnitMap Λ R I n L φ) ≫ z) ht
    dsimp only [f, e, s, P, N, U, t, pairIdealOnePoleUnitMap,
      AlgebraicGeometry.Scheme.Modules, inferInstance, Invertible.tensorLineBundle,
      Invertible.pullbackLineBundle, Subtype.val] at hp hcongr ⊢
    exact hcongr.trans hp
  rw [hp']
  calc
    _ = e.hom.app M ≫
        ((pullback (Spec.map σ)).map φ ≫
          (positiveCartierTensorSection (Spec (.of S)) ((pullback f).obj Q)
            ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app
              ((pullback (Spec.map σ)).obj L.val) ≫
          (tensorSheafBraiding (Spec (.of S)) ((pullback f).obj Q)
            ((pullback (Spec.map σ)).obj L.val)).hom) :=
      congrArg (fun z => e.hom.app M ≫ z) hu
    _ = _ := by rw [← Category.assoc, ← hn, Category.assoc, Functor.comp_map]

end AlgebraicGeometry.Scheme.Blowup.RegularPair
