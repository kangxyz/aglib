/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionComparison
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HomologyCoherence

/-! # Higher exchange and actual resolution homology

The original single/homology comparisons turn the actual resolution exchange
equation into the literal map on homology of the original resolution complexes.
The transported arrow is supplied together with its exact defining formula;
no comparison isomorphism or cohomological vanishing is hypothesized.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

section ExactComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  (G : A ⥤ C) [G.Additive] [G.PreservesHomology]

/-- The inverse native homology comparison retains the actual exact-complex map. -/
theorem rightDerivedFunctorPlusHomologyIso_inv_exactComparison
    (n : ℤ) (K : CochainComplex.Plus A) :
    G.map ((DerivedCategory.Plus.homologyFunctorFactors (A := A) n).inv.app K) ≫
        (G.rightDerivedFunctorPlusHomologyIso n).inv.app (DerivedCategory.Plus.Q.obj K) ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlusExactComparison.hom.app K) =
      (G.mapCochainComplexPlusHomologyIso n).inv.app K ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := C) n).inv.app
          (G.mapCochainComplexPlus.obj K) := by
  apply (cancel_mono
    ((DerivedCategory.Plus.homologyFunctorFactors (A := C) n).hom.app
      (G.mapCochainComplexPlus.obj K) ≫
      (G.mapCochainComplexPlusHomologyIso n).hom.app K)).mp
  simp only [Category.assoc]
  rw [← G.rightDerivedFunctorPlusHomologyIso_exactComparison n K]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, ← G.map_comp,
    G.map_id]
  rfl

end ExactComparison

section Exchange

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D] [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂)
  (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
    H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)
  {M : B} (I : InjectiveResolution M) (J : InjectiveResolution (H.obj M))
  (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus)
  (q : ℕ)
  (b : G.obj ((R₁.rightDerived q).obj M) ⟶ (R₂.rightDerived q).obj (H.obj M))

/-- The original right-derived arrow computed on the actual resolution homology. -/
def HigherResolutionExchangeEquation : Prop :=
  b ≫ (J.isoRightDerivedObjCochain R₂ q).hom =
    G.map (I.isoRightDerivedObjCochain R₁ q).hom ≫
      (G.mapCochainComplexPlusHomologyIso (q : ℤ)).inv.app
        (R₁.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      homologyMap
        (((exchangeOnComplexes R₁ R₂ G H α).app I.cochainComplexPlus ≫
          R₂.mapCochainComplexPlus.map φ).hom) (q : ℤ)

/-- Original derived exchange on resolutions gives its original higher arrow,
using the exact five factors already defining that arrow. -/
theorem higherResolutionExchangeEquation_of_transport
    (hres : ResolutionExchangeEquation R₁ R₂ G H α β I J φ)
    (hb : b =
      G.map ((R₁.rightDerivedSingleHomologyIso q).hom.app M) ≫
        (G.rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
          (R₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
          (β.app ((DerivedCategory.Plus.singleFunctor B 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
          (R₂.rightDerivedFunctorPlus.map ((H.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        (R₂.rightDerivedSingleHomologyIso q).inv.app (H.obj M)) :
    HigherResolutionExchangeEquation R₁ R₂ G H α I J φ q b := by
  let HA := DerivedCategory.Plus.homologyFunctor A (q : ℤ)
  let HC := DerivedCategory.Plus.homologyFunctor C (q : ℤ)
  let PA := DerivedCategory.Plus.homologyFunctorFactors (A := A) (q : ℤ)
  let PC := DerivedCategory.Plus.homologyFunctorFactors (A := C) (q : ℤ)
  let E := G.rightDerivedFunctorPlusHomologyIso (q : ℤ)
  let KI := R₁.mapCochainComplexPlus.obj I.cochainComplexPlus
  let KJ := R₂.mapCochainComplexPlus.obj J.cochainComplexPlus
  let ψ := (exchangeOnComplexes R₁ R₂ G H α).app I.cochainComplexPlus ≫
    R₂.mapCochainComplexPlus.map φ
  have hi : (R₁.rightDerivedSingleHomologyIso q).hom.app M =
      (I.isoRightDerivedObjCochain R₁ q).hom ≫ PA.inv.app KI ≫
        HA.map (I.rightDerivedFunctorPlusIso R₁).hom :=
    R₁.rightDerivedSingleHomologyIso_hom_app I q
  have hj : (J.isoRightDerivedObjCochain R₂ q).hom ≫ PC.inv.app KJ ≫
      HC.map (J.rightDerivedFunctorPlusIso R₂).hom =
        (R₂.rightDerivedSingleHomologyIso q).hom.app (H.obj M) :=
    (R₂.rightDerivedSingleHomologyIso_hom_app J q).symm
  have hn := E.inv.naturality (I.rightDerivedFunctorPlusIso R₁).hom
  simp only [Functor.comp_map] at hn
  have hr := congrArg HC.map hres
  simp only [Functor.map_comp] at hr
  have hp := PC.inv.naturality ψ
  change homologyMap ψ.hom (q : ℤ) ≫ PC.inv.app KJ =
    PC.inv.app (G.mapCochainComplexPlus.obj KI) ≫
      HC.map (DerivedCategory.Plus.Q.map ψ) at hp
  dsimp only [HigherResolutionExchangeEquation]
  apply (cancel_mono (PC.inv.app KJ ≫
    HC.map (J.rightDerivedFunctorPlusIso R₂).hom)).mp
  simp only [Category.assoc]
  rw [hj, hb]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hi]
  simp only [G.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hr]
  rw [reassoc_of% G.rightDerivedFunctorPlusHomologyIso_inv_exactComparison (q : ℤ) KI]
  simpa only [ψ, HC, PC, KI, KJ, Functor.map_comp, Category.assoc,
    Functor.comp_obj, Category.comp_id] using
    congrArg (fun a => G.map (I.isoRightDerivedObjCochain R₁ q).hom ≫
      (G.mapCochainComplexPlusHomologyIso (q : ℤ)).inv.app KI ≫ a ≫
        HC.map (J.rightDerivedFunctorPlusIso R₂).hom) hp.symm

end Exchange

end CategoryTheory.Functor
