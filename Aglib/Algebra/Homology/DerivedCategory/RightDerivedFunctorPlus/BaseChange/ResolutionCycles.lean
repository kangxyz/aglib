/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionHomology
public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components

/-! # The original resolution exchange on native cycles

The shared original resolution-homology equation determines its exact action
on native cycles. This is pure exact-functor calculus: the cycle projection and
actual complex map are unchanged, and no new comparison is defined.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives B] [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive] [G.PreservesHomology]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂)
  {M : B} (I : InjectiveResolution M) (J : InjectiveResolution (H.obj M))
  (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus)
  (q : ℕ) (b : G.obj ((R₁.rightDerived q).obj M) ⟶ (R₂.rightDerived q).obj (H.obj M))

/-- The original higher map applied to an actual projected cycle is the
projection of its actual exact-image cycle followed by the actual complex map. -/
theorem higherResolutionExchangeEquation_cycles
    (hb : HigherResolutionExchangeEquation R₁ R₂ G H α I J φ q b) :
    let K := (R₁.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let T := (R₂.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := ((exchangeOnComplexes R₁ R₂ G H α).app I.cochainComplexPlus ≫
      R₂.mapCochainComplexPlus.map φ).hom
    G.map (K.homologyπ (q : ℤ)) ≫ G.map (I.isoRightDerivedObjCochain R₁ q).inv ≫
        b ≫ (J.isoRightDerivedObjCochain R₂ q).hom =
      ((K.sc (q : ℤ)).mapCyclesIso G).inv ≫ cyclesMap ψ (q : ℤ) ≫
        T.homologyπ (q : ℤ) := by
  dsimp only
  let K := (R₁.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let ψ := ((exchangeOnComplexes R₁ R₂ G H α).app I.cochainComplexPlus ≫
    R₂.mapCochainComplexPlus.map φ).hom
  change b ≫ (J.isoRightDerivedObjCochain R₂ q).hom =
    G.map (I.isoRightDerivedObjCochain R₁ q).hom ≫
      ((K.sc (q : ℤ)).mapHomologyIso G).inv ≫ homologyMap ψ (q : ℤ) at hb
  have hc : G.map (I.isoRightDerivedObjCochain R₁ q).inv ≫
      G.map (I.isoRightDerivedObjCochain R₁ q).hom = 𝟙 _ := by
    rw [← G.map_comp, Iso.inv_hom_id, G.map_id]
  have hp : G.map (K.homologyπ (q : ℤ)) ≫ ((K.sc (q : ℤ)).mapHomologyIso G).inv =
      ((K.sc (q : ℤ)).mapCyclesIso G).inv ≫
        ((G.mapHomologicalComplex (.up ℤ)).obj K).homologyπ (q : ℤ) :=
    ShortComplex.map_homologyπ_mapHomologyIso_inv G (K.sc (q : ℤ))
  rw [hb, reassoc_of% hc, reassoc_of% hp, homologyπ_naturality]
  rfl

end CategoryTheory.Functor
