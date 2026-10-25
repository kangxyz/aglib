/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ComplexComponents

/-! # Original exchange on actual section complexes

An underived section equation lifts to the actual bounded-below complexes.
The source and target complex maps remain explicit aliases, identified by
component equations. All termwise functor conversions occur before geometric
specialization; no new exchange or comparison map is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor

variable {A B C D E : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  (ΓA : A ⥤ E) (ΓB : B ⥤ E) (ΓC : C ⥤ E) (ΓD : D ⥤ E)
  [ΓA.Additive] [ΓB.Additive] [ΓC.Additive] [ΓD.Additive]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂) (e₁ : R₁ ⋙ ΓA ≅ ΓB) (e₂ : R₂ ⋙ ΓC ≅ ΓD)
  (a : ∀ M, ΓA.obj M ⟶ ΓC.obj (G.obj M))
  (b : ∀ M, ΓB.obj M ⟶ ΓD.obj (H.obj M))

/-- The actual whole-complex section equation follows from the original
underived equation and the components of the two actual section maps. -/
theorem exchangeOnComplexes_sections
    (hα : ∀ M, a (R₁.obj M) ≫ ΓC.map (α.app M) ≫ e₂.hom.app (H.obj M) =
      e₁.hom.app M ≫ b M)
    (K : CochainComplex.Plus B) (L : CochainComplex.Plus D)
    (φ : H.mapCochainComplexPlus.obj K ⟶ L)
    (aK : ΓA.mapCochainComplexPlus.obj (R₁.mapCochainComplexPlus.obj K) ⟶
      ΓC.mapCochainComplexPlus.obj
        (G.mapCochainComplexPlus.obj (R₁.mapCochainComplexPlus.obj K)))
    (bK : ΓB.mapCochainComplexPlus.obj K ⟶
      ΓD.mapCochainComplexPlus.obj (H.mapCochainComplexPlus.obj K))
    (ha : ∀ n, aK.hom.f n = a (R₁.obj (K.obj.X n)))
    (hb : ∀ n, bK.hom.f n = b (K.obj.X n)) :
    aK ≫ ΓC.mapCochainComplexPlus.map
        ((exchangeOnComplexes R₁ R₂ G H α).app K ≫ R₂.mapCochainComplexPlus.map φ) ≫
        (NatIso.mapCochainComplexPlus e₂).hom.app L =
      (NatIso.mapCochainComplexPlus e₁).hom.app K ≫ bK ≫
        ΓD.mapCochainComplexPlus.map φ := by
  apply ObjectProperty.hom_ext
  ext1 n
  change aK.hom.f n ≫
      ΓC.map (((exchangeOnComplexes R₁ R₂ G H α).app K).hom.f n ≫
        R₂.map (φ.hom.f n)) ≫ e₂.hom.app (L.obj.X n) =
    e₁.hom.app (K.obj.X n) ≫ bK.hom.f n ≫ ΓD.map (φ.hom.f n)
  rw [ha, hb, exchangeOnComplexes_app_f, ΓC.map_comp, Category.assoc]
  have hn := e₂.hom.naturality (φ.hom.f n)
  simp only [Functor.comp_map] at hn
  rw [hn]
  change a (R₁.obj (K.obj.X n)) ≫ ΓC.map (α.app (K.obj.X n)) ≫
      e₂.hom.app (H.obj (K.obj.X n)) ≫ ΓD.map (φ.hom.f n) =
    e₁.hom.app (K.obj.X n) ≫ b (K.obj.X n) ≫ ΓD.map (φ.hom.f n)
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ ΓD.map (φ.hom.f n)) (hα (K.obj.X n))

end CategoryTheory.Functor
