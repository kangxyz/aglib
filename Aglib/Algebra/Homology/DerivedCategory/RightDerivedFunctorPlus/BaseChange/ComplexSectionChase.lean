/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ComplexSections
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionCycles
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CycleSectionChase

/-! # The full original exchange chase before geometric specialization

Native cycles, mapped-complex terms and the original higher comparison aliases
are normalized while the functors remain abstract. Actual cycle witnesses,
the actual complex equation and the actual projection equation then determine
the original map on higher sections by pure additive-group cancellation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive] [G.PreservesHomology]
  (ΓA : A ⥤ AddCommGrpCat.{v}) (ΓB : B ⥤ AddCommGrpCat.{v})
  (ΓC : C ⥤ AddCommGrpCat.{v}) (ΓD : D ⥤ AddCommGrpCat.{v})
  [ΓA.Additive] [ΓB.Additive] [ΓC.Additive] [ΓD.Additive]
  [ΓC.PreservesMonomorphisms]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂) (e₁ : R₁ ⋙ ΓA ≅ ΓB) (e₂ : R₂ ⋙ ΓC ≅ ΓD)
  (s : ΓA ⟶ G ⋙ ΓC) (t : ΓB ⟶ H ⋙ ΓD)
  (K : CochainComplex.Plus B) (L : CochainComplex.Plus D)
  (φ : H.mapCochainComplexPlus.obj K ⟶ L) (n : ℤ)

/-- The entire original section chase, including cycle inclusion and projection
cancellation, is performed before any concrete derived-model specialization. -/
theorem exchangeOnComplexes_section_chase :
    let KR := (R₁.mapHomologicalComplex (.up ℤ)).obj K.obj
    let TR := (R₂.mapHomologicalComplex (.up ℤ)).obj L.obj
    let ψ := ((exchangeOnComplexes R₁ R₂ G H α).app K ≫
      R₂.mapCochainComplexPlus.map φ).hom
    ∀ {M : A} {N : C} (r : M ≅ KR.homology n) (r' : N ≅ TR.homology n)
      (b : G.obj M ⟶ N)
      (aK : ΓA.mapCochainComplexPlus.obj (R₁.mapCochainComplexPlus.obj K) ⟶
        ΓC.mapCochainComplexPlus.obj
          (G.mapCochainComplexPlus.obj (R₁.mapCochainComplexPlus.obj K)))
      (bK : ΓB.mapCochainComplexPlus.obj K ⟶
        ΓD.mapCochainComplexPlus.obj (H.mapCochainComplexPlus.obj K))
      (_ha : aK.hom.f n = s.app ((R₁.mapCochainComplexPlus.obj K).obj.X n))
      (_hb : bK.hom.f n = t.app (K.obj.X n))
      (_hc : aK ≫ ΓC.mapCochainComplexPlus.map
          ((exchangeOnComplexes R₁ R₂ G H α).app K ≫ R₂.mapCochainComplexPlus.map φ) ≫
          (NatIso.mapCochainComplexPlus e₂).hom.app L =
        (NatIso.mapCochainComplexPlus e₁).hom.app K ≫ bK ≫
          ΓD.mapCochainComplexPlus.map φ)
      (_hp : ΓA.map (KR.homologyπ n) ≫ ΓA.map r.inv ≫ s.app M ≫
          ΓC.map b ≫ ΓC.map r'.hom =
        s.app (KR.cycles n) ≫ ΓC.map
          (((KR.sc n).mapCyclesIso G).inv ≫ cyclesMap ψ n ≫ TR.homologyπ n))
      (x : ΓA.obj M) (y : ΓC.obj N)
      (z : ΓA.obj (KR.cycles n)) (z' : ΓC.obj (TR.cycles n))
      (_hx : ΓA.map r.hom x = ΓA.map (KR.homologyπ n) z)
      (_hy : ΓC.map r'.hom y = ΓC.map (TR.homologyπ n) z')
      (_hz : e₂.hom.app (L.obj.X n) (ΓC.map (TR.iCycles n) z') =
        ΓD.map (φ.hom.f n)
          (t.app (K.obj.X n) (e₁.hom.app (K.obj.X n) (ΓA.map (KR.iCycles n) z)))),
      ΓC.map b (s.app M x) = y := by
  dsimp only
  intro M N r r' b aK bK ha hb hc hp x y z z' hx hy hz
  let KR := (R₁.mapHomologicalComplex (.up ℤ)).obj K.obj
  let TR := (R₂.mapHomologicalComplex (.up ℤ)).obj L.obj
  let ψ : (G.mapHomologicalComplex (.up ℤ)).obj KR ⟶ TR :=
    ((exchangeOnComplexes R₁ R₂ G H α).app K ≫ R₂.mapCochainComplexPlus.map φ).hom
  let c : G.obj (KR.cycles n) ⟶ TR.cycles n :=
    ((KR.sc n).mapCyclesIso G).inv ≫ cyclesMap ψ n
  have hci : c ≫ TR.iCycles n = G.map (KR.iCycles n) ≫ ψ.f n := by
    dsimp only [c]
    rw [Category.assoc, cyclesMap_i]
    change ((KR.sc n).mapCyclesIso G).inv ≫ ((KR.sc n).map G).iCycles ≫ ψ.f n = _
    rw [← Category.assoc, ShortComplex.mapCyclesIso_inv_iCycles]
    rfl
  have hi : (s.app (KR.cycles n) ≫ ΓC.map c) ≫ ΓC.map (TR.iCycles n) =
      ΓA.map (KR.iCycles n) ≫ (s.app (KR.X n) ≫ ΓC.map (ψ.f n)) := by
    rw [Category.assoc, ← ΓC.map_comp, hci, ΓC.map_comp]
    have hn := s.naturality (KR.iCycles n)
    change ΓA.map (KR.iCycles n) ≫ s.app (KR.X n) =
      s.app (KR.cycles n) ≫ ΓC.map (G.map (KR.iCycles n)) at hn
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ ΓC.map (ψ.f n)) hn.symm).trans (Category.assoc _ _ _))
  have hm := congrArg (fun k => k.hom.f n) hc
  change aK.hom.f n ≫ ΓC.map (ψ.f n) ≫ e₂.hom.app (L.obj.X n) =
    e₁.hom.app (K.obj.X n) ≫ bK.hom.f n ≫ ΓD.map (φ.hom.f n) at hm
  rw [ha, hb] at hm
  change s.app (KR.X n) ≫ ΓC.map (ψ.f n) ≫ e₂.hom.app (L.obj.X n) =
    e₁.hom.app (K.obj.X n) ≫ t.app (K.obj.X n) ≫ ΓD.map (φ.hom.f n) at hm
  have ht : (s.app (KR.X n) ≫ ΓC.map (ψ.f n)) ≫ e₂.hom.app (L.obj.X n) =
      e₁.hom.app (K.obj.X n) ≫ (t.app (K.obj.X n) ≫ ΓD.map (φ.hom.f n)) := by
    simpa only [Category.assoc] using hm
  have hπ : ΓA.map (KR.homologyπ n) ≫ (ΓA.mapIso r).inv ≫
        (s.app M ≫ ΓC.map b) ≫ (ΓC.mapIso r').hom =
      (s.app (KR.cycles n) ≫ ΓC.map c) ≫ ΓC.map (TR.homologyπ n) := by
    simpa only [Functor.mapIso_inv, Functor.mapIso_hom, c, ΓC.map_comp,
      Category.assoc] using hp
  exact cycle_section_chase (ΓA.map (KR.iCycles n)) (ΓC.map (TR.iCycles n))
    (ΓA.map (KR.homologyπ n)) (ΓC.map (TR.homologyπ n)) (ΓA.mapIso r) (ΓC.mapIso r')
    (s.app (KR.cycles n) ≫ ΓC.map c) (s.app (KR.X n) ≫ ΓC.map (ψ.f n))
    (s.app M ≫ ΓC.map b) (e₁.hom.app (K.obj.X n)) (e₂.app (L.obj.X n))
    (t.app (K.obj.X n) ≫ ΓD.map (φ.hom.f n)) hi ht hπ x y z z' hx hy hz

end CategoryTheory.Functor
