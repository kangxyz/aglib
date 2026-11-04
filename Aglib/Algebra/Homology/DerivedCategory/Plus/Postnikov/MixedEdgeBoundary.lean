/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdgeTrace
public import Aglib.CategoryTheory.Shift.TransportComposition

/-! The signed trace of the original restricted connecting morphism. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Abelian

@[expose] public noncomputable section

namespace DerivedCategory.Plus

universe u v w e

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [HasExt.{e} C]

/-- A restriction of an original connecting arrow and an original trace evaluate to
the negative pushout of the corresponding short-exact extension. -/
theorem mixedEdgeTrace_boundary_of_comparison
    (T : Triangle (Plus C)) (hT : T ∈ distTriang (Plus C))
    [T.obj₁.IsLE 1] [T.obj₂.IsLE 1] [T.obj₃.IsLE 1]
    {S : ShortComplex C} (hS : S.ShortExact)
    (a : (homologyFunctor C 1).obj T.obj₁ ⟶ S.X₁)
    (b : (homologyFunctor C 1).obj T.obj₂ ⟶ S.X₂)
    (c : (homologyFunctor C 1).obj T.obj₃ ⟶ S.X₃)
    (h₁ : (homologyFunctor C 1).map T.mor₁ ≫ b = a ≫ S.f)
    (h₂ : (homologyFunctor C 1).map T.mor₂ ≫ c = b ≫ S.g)
    {W V : C} (x : (singleFunctor C 1).obj W ⟶ T.obj₃) (j : W ⟶ S.X₃)
    (hx : (homologyFunctor C 1).map x ≫ c =
      (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app W ≫ j)
    {B K : Plus C} (i : T.obj₁ ⟶ K) (k : T.obj₃ ⟶ B)
    (δ : ShiftedHom B K (1 : ℤ)) (hδ : k ≫ δ = T.mor₃ ≫ i⟦(1 : ℤ)⟧')
    (θ : S.X₁ ⟶ V) (t : ShiftedHom K ((singleFunctor C 0).obj V) (-1 : ℤ))
    (ht : (homologyFunctor C 1).map
      (i ≫ t ≫ (((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app V).hom) ≫
        (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app V = a ≫ θ)
    (z : ShiftedHom ((singleFunctor C 0).obj W) B (1 : ℤ))
    (hz :
      let F := singleFunctor C 0
      let η := (singleFunctors C).shiftIso (-1) 1 0 (by omega)
      let adj : shiftFunctor (Plus C) (-1 : ℤ) ⊣ shiftFunctor (Plus C) (1 : ℤ) :=
        (shiftEquiv' (Plus C) (-1 : ℤ) 1 (by omega)).toAdjunction
      z = adj.homEquiv (F.obj W) B (η.hom.app W ≫ x ≫ k))
    (y : Ext.{e} W V 1)
    (hy : y.homPlus = (z.comp δ (by omega : 1 + 1 = (2 : ℤ))).comp t
      (by omega : (-1 : ℤ) + 2 = 1)) :
    y = -(((Ext.mk₀ j).comp hS.extClass (zero_add 1)).comp (Ext.mk₀ θ) (add_zero 1)) := by
  let F := singleFunctor C 0
  let U := F.obj W
  let η := (singleFunctors C).shiftIso (-1) 1 0 (by omega)
  let adj : shiftFunctor (Plus C) (-1 : ℤ) ⊣ shiftFunctor (Plus C) (1 : ℤ) :=
    (shiftEquiv' (Plus C) (-1 : ℤ) 1 (by omega)).toAdjunction
  let z₀ : ShiftedHom U T.obj₃ (1 : ℤ) := adj.homEquiv U T.obj₃ (η.hom.app W ≫ x)
  have hz' : z = z₀ ≫ k⟦(1 : ℤ)⟧' := by
    rw [hz]
    change (adj.homEquiv U B) (η.hom.app W ≫ x ≫ k) = _
    rw [← Category.assoc]
    exact adj.homEquiv_naturality_right (η.hom.app W ≫ x) k
  have hc := ShiftedHom.comp_trace_of_square z₀ T.mor₃ k i δ hδ t
    (by omega : (-1 : ℤ) + 1 + 1 = 1)
  have hm := mixedEdge_precomp_topSingle_shiftedTrace T hT hS a b c h₁ h₂ x j hx θ
    (i ≫ t : ShiftedHom T.obj₁ (F.obj V) (-1 : ℤ)) (by
      simpa only [Category.assoc] using ht)
  apply (Ext.homPlusAddEquiv 1).injective
  rw [map_neg, Ext.homPlusAddEquiv_apply, Ext.homPlusAddEquiv_apply,
    Ext.homPlus_transport_degreeZero, Ext.homPlus_extClass, hy, hz', hc]
  exact hm

end DerivedCategory.Plus
