/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FiniteSource.Derived

/-! # Coefficient naturality of the installed open-homology comparison

The three original component naturality equations prove naturality of the actual
installed map. No quasicoherence, resolution choice, or compatibility premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance openNaturalityStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- The installed open-homology arrow is natural in every actual coefficient
map, through the original derived single and restriction functors. -/
@[reassoc]
theorem derivedClosedImmersionRightAdjointOpenHomologyIso_naturality
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (i : U ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] [IsClosedImmersion i] [IsClosedImmersion b]
    (h : IsPullback a b i j) {L L' : X.Modules} (μ : L ⟶ L') (n : ℤ) :
    (restrictFunctor a).map
        ((DerivedCategory.Plus.homologyFunctor U.Modules n).map
          ((derivedClosedImmersionRightAdjointPlus i).map
            ((DerivedCategory.Plus.singleFunctor X.Modules 0).map μ))) ≫
      (derivedClosedImmersionRightAdjointOpenHomologyIso a b i j h L' n).hom =
    (derivedClosedImmersionRightAdjointOpenHomologyIso a b i j h L n).hom ≫
      (DerivedCategory.Plus.homologyFunctor W.Modules n).map
        ((derivedClosedImmersionRightAdjointPlus b).map
          ((DerivedCategory.Plus.singleFunctor V.Modules 0).map ((restrictFunctor j).map μ))) := by
  let S := DerivedCategory.Plus.singleFunctor X.Modules 0
  let S' := DerivedCategory.Plus.singleFunctor V.Modules 0
  let F := derivedClosedImmersionRightAdjointPlus i
  let B := derivedClosedImmersionRightAdjointPlus b
  let G := restrictFunctor a
  let J := restrictFunctor j
  let Gd := G.rightDerivedFunctorPlus
  let Jd := J.rightDerivedFunctorPlus
  let HU := DerivedCategory.Plus.homologyFunctor U.Modules n
  let HW := DerivedCategory.Plus.homologyFunctor W.Modules n
  let E := G.rightDerivedFunctorPlusHomologyIso n
  let O := derivedClosedImmersionRightAdjointOpenIso a b i j h
  let C := J.rightDerivedFunctorPlusSingleIso 0
  let x := F.map (S.map μ)
  let y := B.map (S'.map (J.map μ))
  let p := Gd.map x
  let q := B.map (Jd.map (S.map μ))
  let o := O.hom.app (S.obj L)
  let o' := O.hom.app (S.obj L')
  let s := B.map (C.hom.app L)
  let s' := B.map (C.hom.app L')
  let e : G.obj (HU.obj (F.obj (S.obj L))) ⟶ HW.obj (Gd.obj (F.obj (S.obj L))) :=
    E.inv.app (F.obj (S.obj L))
  let e' : G.obj (HU.obj (F.obj (S.obj L'))) ⟶ HW.obj (Gd.obj (F.obj (S.obj L'))) :=
    E.inv.app (F.obj (S.obj L'))
  have he : G.map (HU.map x) ≫ e' = e ≫ HW.map p := E.inv.naturality x
  have ho : p ≫ o' = o ≫ q := O.hom.naturality (S.map μ)
  have hs : q ≫ s' = s ≫ y := by
    have hc : Jd.map (S.map μ) ≫ C.hom.app L' =
        C.hom.app L ≫ S'.map (J.map μ) := by
      simpa only [Functor.comp_map] using C.hom.naturality μ
    exact Eq.trans (B.map_comp (Jd.map (S.map μ)) (C.hom.app L')).symm
      (Eq.trans (congrArg B.map hc)
        (B.map_comp (C.hom.app L) (S'.map (J.map μ))))
  have hm₁ : p ≫ (o' ≫ s') = (p ≫ o') ≫ s' := (Category.assoc p o' s').symm
  have hm₂ : (p ≫ o') ≫ s' = (o ≫ q) ≫ s' := congrArg (fun k => k ≫ s') ho
  have hm₃ : (o ≫ q) ≫ s' = o ≫ (q ≫ s') := Category.assoc o q s'
  have hm₄ : o ≫ (q ≫ s') = o ≫ (s ≫ y) := congrArg (fun k => o ≫ k) hs
  have hm₅ : o ≫ (s ≫ y) = (o ≫ s) ≫ y := (Category.assoc o s y).symm
  have hm : p ≫ (o' ≫ s') = (o ≫ s) ≫ y :=
    Eq.trans hm₁ (Eq.trans hm₂ (Eq.trans hm₃ (Eq.trans hm₄ hm₅)))
  have hmH : HW.map p ≫ HW.map (o' ≫ s') = HW.map (o ≫ s) ≫ HW.map y :=
    Eq.trans (HW.map_comp p (o' ≫ s')).symm
      (Eq.trans (congrArg HW.map hm) (HW.map_comp (o ≫ s) y))
  have h₁ : G.map (HU.map x) ≫ (e' ≫ HW.map (o' ≫ s')) =
      (G.map (HU.map x) ≫ e') ≫ HW.map (o' ≫ s') :=
    (Category.assoc _ _ _).symm
  have h₂ : (G.map (HU.map x) ≫ e') ≫ HW.map (o' ≫ s') =
      (e ≫ HW.map p) ≫ HW.map (o' ≫ s') :=
    congrArg (fun k => k ≫ HW.map (o' ≫ s')) he
  have h₃ : (e ≫ HW.map p) ≫ HW.map (o' ≫ s') =
      e ≫ (HW.map p ≫ HW.map (o' ≫ s')) := Category.assoc _ _ _
  have h₄ : e ≫ (HW.map p ≫ HW.map (o' ≫ s')) =
      e ≫ (HW.map (o ≫ s) ≫ HW.map y) := congrArg (fun k => e ≫ k) hmH
  have h₅ : e ≫ (HW.map (o ≫ s) ≫ HW.map y) =
      (e ≫ HW.map (o ≫ s)) ≫ HW.map y := (Category.assoc _ _ _).symm
  have hl : (derivedClosedImmersionRightAdjointOpenHomologyIso a b i j h L n).hom =
      e ≫ HW.map (o ≫ s) := derivedClosedImmersionRightAdjointOpenHomologyIso_hom a b i j h L n
  have hl' : (derivedClosedImmersionRightAdjointOpenHomologyIso a b i j h L' n).hom =
      e' ≫ HW.map (o' ≫ s') := derivedClosedImmersionRightAdjointOpenHomologyIso_hom a b i j h L' n
  exact Eq.trans (congrArg (fun k => G.map (HU.map x) ≫ k) hl')
    (Eq.trans (Eq.trans h₁ (Eq.trans h₂ (Eq.trans h₃ (Eq.trans h₄ h₅))))
      (congrArg (fun k => k ≫ HW.map y) hl.symm))

end AlgebraicGeometry.Scheme.Modules
