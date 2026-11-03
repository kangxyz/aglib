/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorChartSquare
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenArrow
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorPullbackComposition
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorPullbackCongruence
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / ExteriorOpenSquare

Source: `IntegralTrace/PairIdealRawOpenTransport.lean`.
Incoming SHA256: `95a01181178bff0fe417dcf0273c622e1a9a48b0b95d8ca1912cde6b78e160ae`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom

universe u vK

namespace AlgebraicGeometry.Scheme.Modules.Differentials

section RawComparison

variable {Λ : CommRingCat.{u}} {X Y U Z : Scheme.{u}}
  (a : X ⟶ Spec Λ) (aU : U ⟶ Spec Λ)
  (j : U ⟶ X) [IsOpenImmersion j] (ha : j ≫ a = aU)
  (b : Y ⟶ X) (d : Z ⟶ U) (q : Z ⟶ Y) [IsOpenImmersion q]
  (hq : q ≫ b = d ≫ j) (n : ℕ)

/-- The original base raw comparison, including the actual structural congruence. -/
def rawOpenBaseIso :
    (pullback j).obj (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≅
      moduleExteriorPower U (relativeDifferentialSheaf aU) n :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app _).symm ≪≫
    rawFormsOpenIso a j n ≪≫ (moduleExteriorPowerFunctor U n).mapIso
      (relativeDifferentialCongrIso (j ≫ a) ha)

/-- The explicit native source comparison retains all three actual congruences. -/
def rawOpenSourceIso :
    (pullback q).obj (moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n) ≅
      moduleExteriorPower Z (relativeDifferentialSheaf (d ≫ aU)) n :=
  ((Scheme.Modules.restrictFunctorIsoPullback q).app _).symm ≪≫
    rawFormsOpenIso (b ≫ a) q n ≪≫
      (moduleExteriorPowerFunctor Z n).mapIso
        (relativeDifferentialCongrIso (q ≫ (b ≫ a))
          ((Category.assoc q b a).symm.trans (congrArg (fun t => t ≫ a) hq))) ≪≫
      (moduleExteriorPowerFunctor Z n).mapIso
        (relativeDifferentialCongrIso ((d ≫ j) ≫ a) (Category.assoc d j a)) ≪≫
      (moduleExteriorPowerFunctor Z n).mapIso
        (relativeDifferentialCongrIso (d ≫ (j ≫ a)) (congrArg (fun t => d ≫ t) ha))

/-- Original raw arrows satisfy the complete chart square; no square is an input. -/
theorem rawOpenSourceIso_pullback :
    (pullback q).map (rawFormsPullback a b n) ≫
        (rawOpenSourceIso a aU j ha b d q hq n).hom =
      (pullbackComp q b ≪≫ pullbackCongr hq ≪≫ (pullbackComp d j).symm).hom.app
          (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≫
        (pullback d).map (rawOpenBaseIso a aU j ha n).hom ≫
          rawFormsPullback aU d n := by
  let G := (moduleExteriorPowerFunctor U n).map
    (relativeDifferentialCongrIso (j ≫ a) ha).hom
  let H := (moduleExteriorPowerFunctor Z n).map
    (relativeDifferentialCongrIso (d ≫ (j ≫ a)) (congrArg (fun t => d ≫ t) ha)).hom
  have hf : (rawOpenBaseIso a aU j ha n).hom = rawFormsPullback a j n ≫ G := by
    have ho :
        (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
            (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≫
          (rawFormsOpenIso a j n).hom = rawFormsPullback a j n := by
      rw [← rawFormsPullback_restrict a j n, Iso.inv_hom_id_app_assoc]
    simpa only [rawOpenBaseIso, G, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
      Functor.mapIso_hom, Category.assoc] using congrArg (fun z => z ≫ G) ho
  let G₁ := (moduleExteriorPowerFunctor Z n).map
    (relativeDifferentialCongrIso ((d ≫ j) ≫ a) (Category.assoc d j a)).hom
  let A := (pullbackComp q b).hom.app
      (moduleExteriorPower X (relativeDifferentialSheaf a) n) ≫
    (pullbackCongr hq).hom.app (moduleExteriorPower X (relativeDifferentialSheaf a) n)
  let D := (pullbackComp d j).inv.app
    (moduleExteriorPower X (relativeDifferentialSheaf a) n)
  have ho := congrArg (fun z => z ≫ G₁ ≫ H)
    (rawFormsPullback_openTriangle a b q (d ≫ j) hq n)
  have hc := congrArg (fun z => A ≫ z ≫ H)
    (rawFormsPullback_comp a j d n).symm
  have he := congrArg (fun z => A ≫ D ≫ (pullback d).map (rawFormsPullback a j n) ≫ z)
    (rawFormsPullback_congr ha d n).symm
  calc
    _ = A ≫ rawFormsPullback a (d ≫ j) n ≫ G₁ ≫ H := by
      simpa only [rawOpenSourceIso, A, G₁, H, Iso.trans_hom, Iso.symm_hom,
        Iso.app_inv, Functor.mapIso_hom, Category.assoc] using ho
    _ = A ≫ D ≫ (pullback d).map (rawFormsPullback a j n) ≫
        rawFormsPullback (j ≫ a) d n ≫ H := by
      simpa only [A, D, G₁, Category.assoc] using hc
    _ = A ≫ D ≫ (pullback d).map (rawFormsPullback a j n) ≫
        (pullback d).map G ≫ rawFormsPullback aU d n := by
      simpa only [G, H, Category.assoc] using he
    _ = _ := by
      rw [hf, Functor.map_comp]
      simp only [A, D, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]

end RawComparison

end AlgebraicGeometry.Scheme.Modules.Differentials
