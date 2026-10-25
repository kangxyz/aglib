/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ComplexSectionChase
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionCycleSections
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans

/-! # Original resolution exchange under actual section isomorphisms

Actual section comparison isomorphisms, the original underived equation and
actual resolution cycles determine the original higher arrow. All complex and
cycle transports are performed before geometric specialization.
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
  [EnoughInjectives B] [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive] [G.PreservesHomology]
  (ΓA : A ⥤ AddCommGrpCat.{v}) (ΓB : B ⥤ AddCommGrpCat.{v})
  (ΓC : C ⥤ AddCommGrpCat.{v}) (ΓD : D ⥤ AddCommGrpCat.{v})
  [ΓA.Additive] [ΓB.Additive] [ΓC.Additive] [ΓD.Additive]
  [ΓC.PreservesMonomorphisms]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂) (e₁ : R₁ ⋙ ΓA ≅ ΓB) (e₂ : R₂ ⋙ ΓC ≅ ΓD)
  (s : G ⋙ ΓC ≅ ΓA) (t : H ⋙ ΓD ≅ ΓB)

/-- Genuine original resolution cycles and an ordinary section-isomorphism
square compute the SAME higher arrow on every section represented by them. -/
theorem higherResolutionExchangeEquation_section_chase
    (hα : ∀ M, ΓC.map (α.app M) ≫ e₂.hom.app (H.obj M) ≫ t.hom.app M =
      s.hom.app (R₁.obj M) ≫ e₁.hom.app M)
    {M : B} (I : InjectiveResolution M) (J : InjectiveResolution (H.obj M))
    (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus)
    (q : ℕ) (b : G.obj ((R₁.rightDerived q).obj M) ⟶ (R₂.rightDerived q).obj (H.obj M))
    (hb : HigherResolutionExchangeEquation R₁ R₂ G H α I J φ q b) :
    let K := (R₁.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let T := (R₂.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    ∀ (x : ΓA.obj ((R₁.rightDerived q).obj M))
      (y : ΓC.obj ((R₂.rightDerived q).obj (H.obj M)))
      (z : ΓA.obj (K.cycles (q : ℤ))) (z' : ΓC.obj (T.cycles (q : ℤ)))
      (_hx : ΓA.map (I.isoRightDerivedObjCochain R₁ q).hom x =
        ΓA.map (K.homologyπ (q : ℤ)) z)
      (_hy : ΓC.map (J.isoRightDerivedObjCochain R₂ q).hom y =
        ΓC.map (T.homologyπ (q : ℤ)) z')
      (_hz : e₂.hom.app (J.cochainComplex.X (q : ℤ))
          (ΓC.map (T.iCycles (q : ℤ)) z') =
        ΓD.map (φ.hom.f (q : ℤ))
          (t.inv.app (I.cochainComplex.X (q : ℤ))
            (e₁.hom.app (I.cochainComplex.X (q : ℤ))
              (ΓA.map (K.iCycles (q : ℤ)) z)))),
      ΓC.map b (s.inv.app ((R₁.rightDerived q).obj M) x) = y := by
  dsimp only
  intro x y z z' hx hy hz
  have hs (N : B) : s.inv.app (R₁.obj N) ≫ ΓC.map (α.app N) ≫
      e₂.hom.app (H.obj N) = e₁.hom.app N ≫ t.inv.app N := by
    have h := congrArg (fun k => s.inv.app (R₁.obj N) ≫ k ≫ t.inv.app N) (hα N)
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc] at h
    change s.inv.app (R₁.obj N) ≫ ΓC.map (α.app N) ≫
      e₂.hom.app (H.obj N) ≫ 𝟙 (ΓD.obj (H.obj N)) = e₁.hom.app N ≫ t.inv.app N at h
    simpa only [Category.comp_id] using h
  let aK := (NatTrans.mapCochainComplexPlus s.inv).app
    (R₁.mapCochainComplexPlus.obj I.cochainComplexPlus)
  let bK := (NatTrans.mapCochainComplexPlus t.inv).app I.cochainComplexPlus
  exact exchangeOnComplexes_section_chase R₁ R₂ G H ΓA ΓB ΓC ΓD α e₁ e₂ s.inv t.inv
    I.cochainComplexPlus J.cochainComplexPlus φ (q : ℤ)
    (I.isoRightDerivedObjCochain R₁ q) (J.isoRightDerivedObjCochain R₂ q) b aK bK
    (NatTrans.mapCochainComplexPlus_app_f s.inv
      (R₁.mapCochainComplexPlus.obj I.cochainComplexPlus) (q : ℤ))
    (NatTrans.mapCochainComplexPlus_app_f t.inv I.cochainComplexPlus (q : ℤ))
    (exchangeOnComplexes_sections R₁ R₂ G H ΓA ΓB ΓC ΓD α e₁ e₂
      s.inv.app t.inv.app hs I.cochainComplexPlus J.cochainComplexPlus φ aK bK
      (NatTrans.mapCochainComplexPlus_app_f s.inv
        (R₁.mapCochainComplexPlus.obj I.cochainComplexPlus))
      (NatTrans.mapCochainComplexPlus_app_f t.inv I.cochainComplexPlus))
    (higherResolutionExchangeEquation_cycle_sections
      R₁ R₂ G H ΓA ΓC s.inv α I J φ q b hb) x y z z' hx hy hz

end CategoryTheory.Functor
