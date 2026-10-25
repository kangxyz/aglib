/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CyclePairing
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ResolutionSectionChase

/-! # Original resolution exchange directly from representative producers

Pair genuine cycle witnesses and consume them in the original resolution
section chase before geometric specialization. The concrete consumer receives
only the original higher-map equality, not an intermediate cycle existential.
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

/-- The original higher exchange on every original class is computed directly
from actual source and target cycle producers. No geometric witness transport
or representative elimination remains in the specialized conclusion. -/
theorem higherResolutionExchangeEquation_of_representatives
    (hα : ∀ M, ΓC.map (α.app M) ≫ e₂.hom.app (H.obj M) ≫ t.hom.app M =
      s.hom.app (R₁.obj M) ≫ e₁.hom.app M)
    {M : B} (I : InjectiveResolution M) (J : InjectiveResolution (H.obj M))
    (φ : H.mapCochainComplexPlus.obj I.cochainComplexPlus ⟶ J.cochainComplexPlus)
    (q : ℕ) (b : G.obj ((R₁.rightDerived q).obj M) ⟶ (R₂.rightDerived q).obj (H.obj M))
    (hb : HigherResolutionExchangeEquation R₁ R₂ G H α I J φ q b)
    {Coh : Type*} {Rep : Type*} (Q : Rep → Prop) (mk : ∀ r, Q r → Coh)
    (hmk : ∀ c, ∃ r hr, mk r hr = c)
    (x : Coh → ΓA.obj ((R₁.rightDerived q).obj M))
    (y : Coh → ΓC.obj ((R₂.rightDerived q).obj (H.obj M))) :
    let K := (R₁.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let T := (R₂.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    ∀ (a : Rep → ΓA.obj (K.X (q : ℤ)))
      (l : ΓA.obj (K.X (q : ℤ)) → ΓD.obj (J.cochainComplex.X (q : ℤ)))
      (_hl : ∀ u, l u = ΓD.map (φ.hom.f (q : ℤ))
        (t.inv.app (I.cochainComplex.X (q : ℤ))
          (e₁.hom.app (I.cochainComplex.X (q : ℤ)) u)))
      (_hs : ∀ r hr, CycleWitness
        (fun z => ΓA.map (K.iCycles (q : ℤ)) z)
        (fun z => ΓA.map (K.homologyπ (q : ℤ)) z) (a r)
        (ΓA.map (I.isoRightDerivedObjCochain R₁ q).hom (x (mk r hr))))
      (_ht : ∀ r hr, CycleWitness
        (fun z => e₂.hom.app (J.cochainComplex.X (q : ℤ))
          (ΓC.map (T.iCycles (q : ℤ)) z))
        (fun z => ΓC.map (T.homologyπ (q : ℤ)) z) (l (a r))
        (ΓC.map (J.isoRightDerivedObjCochain R₂ q).hom (y (mk r hr)))) (c : Coh),
      ΓC.map b (s.inv.app ((R₁.rightDerived q).obj M) (x c)) = y c := by
  dsimp only
  intro a l hl hs ht c
  let K := (R₁.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let T := (R₂.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  obtain ⟨z, z', hx, hy, hz⟩ := pairedCycles_of_representatives Q mk hmk
    (fun z => ΓA.map (K.iCycles (q : ℤ)) z)
    (fun z => ΓA.map (K.homologyπ (q : ℤ)) z)
    (fun c => ΓA.map (I.isoRightDerivedObjCochain R₁ q).hom (x c))
    (fun z => e₂.hom.app (J.cochainComplex.X (q : ℤ))
      (ΓC.map (T.iCycles (q : ℤ)) z))
    (fun z => ΓC.map (T.homologyπ (q : ℤ)) z)
    (fun c => ΓC.map (J.isoRightDerivedObjCochain R₂ q).hom (y c)) a l hs ht c
  exact higherResolutionExchangeEquation_section_chase
    R₁ R₂ G H ΓA ΓB ΓC ΓD α e₁ e₂ s t hα I J φ q b hb
      (x c) (y c) z z' hx hy (hz.trans (hl _))

end CategoryTheory.Functor
