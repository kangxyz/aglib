/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionCycles

/-! # Original resolution exchange under arbitrary section transformations

The original cycle equation commutes with every actual natural transformation
between section functors. Global sections and literal chart evaluation are
instances of the same formula; no injectivity of an edge map is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor

variable {A B C D E : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives B] [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive] [G.PreservesHomology]
  (ΓA : A ⥤ E) (ΓC : C ⥤ E) (s : ΓA ⟶ G ⋙ ΓC)
  (α : R₁ ⋙ G ⟶ H ⋙ R₂)
  {M : B} (I : InjectiveResolution M) (J : InjectiveResolution (H.obj M))
  (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus)
  (q : ℕ) (b : G.obj ((R₁.rightDerived q).obj M) ⟶ (R₂.rightDerived q).obj (H.obj M))

/-- The actual original higher resolution equation on cycles, after an arbitrary
natural section transformation. The original higher arrow remains unchanged. -/
theorem higherResolutionExchangeEquation_cycle_sections
    (hb : HigherResolutionExchangeEquation R₁ R₂ G H α I J φ q b) :
    let K := (R₁.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let T := (R₂.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let ψ := ((exchangeOnComplexes R₁ R₂ G H α).app I.cochainComplexPlus ≫
      R₂.mapCochainComplexPlus.map φ).hom
    ΓA.map (K.homologyπ (q : ℤ)) ≫
        ΓA.map (I.isoRightDerivedObjCochain R₁ q).inv ≫
        s.app ((R₁.rightDerived q).obj M) ≫ ΓC.map b ≫
        ΓC.map (J.isoRightDerivedObjCochain R₂ q).hom =
      s.app (K.cycles (q : ℤ)) ≫ ΓC.map
        (((K.sc (q : ℤ)).mapCyclesIso G).inv ≫ cyclesMap ψ (q : ℤ) ≫
          T.homologyπ (q : ℤ)) := by
  dsimp only
  let K := (R₁.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  have hc := higherResolutionExchangeEquation_cycles R₁ R₂ G H α I J φ q b hb
  have hs := congrArg ΓC.map hc
  simp only [Functor.map_comp] at hs
  have hr := s.naturality (I.isoRightDerivedObjCochain R₁ q).inv
  have hp := s.naturality (K.homologyπ (q : ℤ))
  simp only [Functor.comp_map] at hr hp
  rw [reassoc_of% hr, reassoc_of% hp]
  rw [hs, ΓC.map_comp, ΓC.map_comp]

end CategoryTheory.Functor
