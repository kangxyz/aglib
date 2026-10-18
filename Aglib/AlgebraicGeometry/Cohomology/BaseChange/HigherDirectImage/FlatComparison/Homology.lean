/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology

/-!
# Inverse homology comparisons for the original exact derived unit

The original homology comparison for an exact functor retains its original
derived unit after inverting the comparison isomorphisms. Naturality gives
the same formula after an actual isomorphism from the localized complex.
These identities normalize the source of the installed flat higher-image map.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory HomologicalComplex

universe u v u' v' w w'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- Inverting the native homology comparisons retains the original exact derived unit. -/
theorem rightDerivedFunctorPlusHomologyIso_inv_unit (n : ℤ) (K : CochainComplex.Plus A) :
    ((K.obj.sc n).mapHomologyIso F).inv ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).inv.app
          (F.mapCochainComplexPlus.obj K) ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          (F.rightDerivedFunctorPlusUnit.app K) =
      F.map ((DerivedCategory.Plus.homologyFunctorFactors (A := A) n).inv.app K) ≫
        (F.rightDerivedFunctorPlusHomologyIso n).inv.app
          (DerivedCategory.Plus.Q.obj K) := by
  let H := DerivedCategory.Plus.homologyFunctor B n
  let PA := (DerivedCategory.Plus.homologyFunctorFactors (A := A) n).app K
  let PB := (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).app
    (F.mapCochainComplexPlus.obj K)
  let d := (K.obj.sc n).mapHomologyIso F
  let E := F.rightDerivedFunctorPlusHomologyIso n
  have hu : H.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        E.hom.app (DerivedCategory.Plus.Q.obj K) ≫ F.map PA.hom = PB.hom ≫ d.hom :=
    F.rightDerivedFunctorPlusHomologyIso_unit n K
  have hi : F.map PA.inv ≫ E.inv.app (DerivedCategory.Plus.Q.obj K) =
      d.inv ≫ PB.inv ≫ H.map (F.rightDerivedFunctorPlusUnit.app K) := by
    apply (cancel_mono (E.hom.app (DerivedCategory.Plus.Q.obj K) ≫ F.map PA.hom)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id, hu]
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  exact hi.symm

/-- The native inverse homology-unit formula is natural after an actual isomorphism
from the original localized complex. -/
theorem rightDerivedFunctorPlusHomologyIso_inv_unit_compIso (n : ℤ)
    (K : CochainComplex.Plus A) (L : DerivedCategory.Plus A)
    (e : DerivedCategory.Plus.Q.obj K ≅ L) :
    ((K.obj.sc n).mapHomologyIso F).inv ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).inv.app
          (F.mapCochainComplexPlus.obj K) ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          (F.rightDerivedFunctorPlusUnit.app K ≫
            F.rightDerivedFunctorPlus.map e.hom) =
      F.map ((DerivedCategory.Plus.homologyFunctorFactors (A := A) n).inv.app K ≫
          (DerivedCategory.Plus.homologyFunctor A n).map e.hom) ≫
        (F.rightDerivedFunctorPlusHomologyIso n).inv.app L := by
  let HA := DerivedCategory.Plus.homologyFunctor A n
  let HB := DerivedCategory.Plus.homologyFunctor B n
  let PA := (DerivedCategory.Plus.homologyFunctorFactors (A := A) n).app K
  let PB := (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).app
    (F.mapCochainComplexPlus.obj K)
  let d := (K.obj.sc n).mapHomologyIso F
  let E := F.rightDerivedFunctorPlusHomologyIso n
  have hn : F.map (HA.map e.hom) ≫ E.inv.app L =
      E.inv.app (DerivedCategory.Plus.Q.obj K) ≫
        HB.map (F.rightDerivedFunctorPlus.map e.hom) := E.inv.naturality e.hom
  have hb : d.inv ≫ PB.inv ≫ HB.map (F.rightDerivedFunctorPlusUnit.app K) =
      F.map PA.inv ≫ E.inv.app (DerivedCategory.Plus.Q.obj K) :=
    F.rightDerivedFunctorPlusHomologyIso_inv_unit n K
  change d.inv ≫ PB.inv ≫ HB.map
      (F.rightDerivedFunctorPlusUnit.app K ≫ F.rightDerivedFunctorPlus.map e.hom) =
    F.map (PA.inv ≫ HA.map e.hom) ≫ E.inv.app L
  calc
    _ = (d.inv ≫ PB.inv ≫ HB.map (F.rightDerivedFunctorPlusUnit.app K)) ≫
        HB.map (F.rightDerivedFunctorPlus.map e.hom) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (F.map PA.inv ≫ E.inv.app (DerivedCategory.Plus.Q.obj K)) ≫
        HB.map (F.rightDerivedFunctorPlus.map e.hom) :=
      congrArg (fun t => t ≫ HB.map (F.rightDerivedFunctorPlus.map e.hom)) hb
    _ = _ := by simp only [Functor.map_comp, Category.assoc, hn]

end CategoryTheory.Functor
