/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdge
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.HomToSingle
public import Aglib.CategoryTheory.Adjunction.ShiftedHom.Contraction
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! The original mixed boundary evaluated by a specified trace. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

@[expose] public noncomputable section

namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The original degree-one map to a shifted single is determined by its first homology. -/
theorem eq_upperHomologyShiftMap_of_homology {K : Plus C} [K.IsLE 1] {M : C}
    (t : K ⟶ ((singleFunctor C 0).obj M)⟦(-1 : ℤ)⟧)
    (a : (homologyFunctor C 1).obj K ⟶ M)
    (h : (homologyFunctor C 1).map
      (t ≫ (((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app M).hom) ≫
        (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app M = a) :
    t = upperHomologyShiftMap K a := by
  let H := homologyFunctor C 1
  let F := singleFunctor C 1
  let e := singleFunctorCompHomologyFunctorIso (C := C) 1
  let η := ((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app M
  apply (cancel_mono η.hom).mp
  apply (ι : Plus C ⥤ DerivedCategory C).map_injective
  apply DerivedCategory.homology_map_injective_to_single_of_isLE _ 1 M
  change H.map (t ≫ η.hom) = H.map (upperHomologyShiftMap K a ≫ η.hom)
  apply (cancel_mono (e.hom.app M)).mp
  change H.map (t ≫ η.hom) ≫ e.hom.app M = _
  rw [h]
  have hn : H.map (F.map a) ≫ e.hom.app M = e.hom.app (H.obj K) ≫ a :=
    e.hom.naturality a
  change a = H.map ((upperHomologyProjection K 1 ≫ F.map a ≫ η.inv) ≫ η.hom) ≫ e.hom.app M
  have hp : H.map (upperHomologyProjection K 1) ≫ e.hom.app (H.obj K) = 𝟙 _ :=
    upperHomologyProjection_homology K 1
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, H.map_comp,
    Category.assoc, hn, ← Category.assoc, hp, Category.id_comp]

/-- The negative mixed boundary is evaluated by any original shifted trace with
its specified first homology value. -/
theorem mixedEdge_precomp_topSingle_trace
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
    (θ : S.X₁ ⟶ V) (t : T.obj₁ ⟶ ((singleFunctor C 0).obj V)⟦(-1 : ℤ)⟧)
    (ht : (homologyFunctor C 1).map
      (t ≫ (((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app V).hom) ≫
        (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app V = a ≫ θ) :
    let F := singleFunctor C 0
    let U := F.obj W
    let I := F.obj V
    let η := (singleFunctors C).shiftIso (-1) 1 0 (by omega)
    let μ := shiftFunctorCompIsoId (Plus C) (-1 : ℤ) 1 (by omega)
    let adj : shiftFunctor (Plus C) (-1 : ℤ) ⊣ shiftFunctor (Plus C) (1 : ℤ) :=
      (shiftEquiv' (Plus C) (-1 : ℤ) 1 (by omega)).toAdjunction
    η.hom.app W ≫ x ≫ T.mor₃ ≫ t⟦(1 : ℤ)⟧' ≫ μ.hom.app I =
      -((adj.homEquiv U I).symm
        (F.map j ≫ hS.singleTrianglePlus.mor₃ ≫ (F.map θ)⟦(1 : ℤ)⟧')) := by
  intro F U I η μ adj
  let K := F.obj S.X₁
  let w := F.map θ
  let t₀ := upperHomologyShiftMap T.obj₁ a
  have htc : t = t₀ ≫ w⟦(-1 : ℤ)⟧' := by
    refine (eq_upperHomologyShiftMap_of_homology t (a ≫ θ) ht).trans ?_
    have h := upperHomologyShiftMap_comm (𝟙 T.obj₁) a (a ≫ θ) θ
      ((congrArg (fun f => f ≫ a ≫ θ) ((homologyFunctor C 1).map_id T.obj₁)).trans
        (Category.id_comp _))
    simpa only [Category.id_comp] using h
  have hm : (w⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫ μ.hom.app I = μ.hom.app K ≫ w :=
    μ.hom.naturality w
  have hd := mixedEdge_precomp_topSingle_inverseAdjunct T hT hS a b c h₁ h₂ x j hx
  let z : U ⟶ K⟦(1 : ℤ)⟧ := F.map j ≫ hS.singleTrianglePlus.mor₃
  change η.hom.app W ≫ x ≫ T.mor₃ ≫ t₀⟦(1 : ℤ)⟧' ≫ μ.hom.app K =
    -((adj.homEquiv U K).symm z) at hd
  calc
    _ = (η.hom.app W ≫ x ≫ T.mor₃ ≫ t₀⟦(1 : ℤ)⟧' ≫ μ.hom.app K) ≫ w := by
      rw [htc, Functor.map_comp]
      simp only [Category.assoc, hm]
    _ = -((adj.homEquiv U I).symm (z ≫ w⟦(1 : ℤ)⟧')) := by
      rw [hd, Preadditive.neg_comp]
      exact congrArg Neg.neg (adj.homEquiv_naturality_right_symm z w).symm
    _ = _ := congrArg (fun t' => -((adj.homEquiv U I).symm t'))
      (Category.assoc (F.map j) hS.singleTrianglePlus.mor₃ (w⟦(1 : ℤ)⟧'))

end DerivedCategory.Plus

namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The original two opposite shifts in a trace retain the original homology value. -/
theorem singleShiftTrace_homology_value (q : ℤ) {U V : C} {K : Plus C}
    (x : (singleFunctor C q).obj U ⟶ K)
    (t : K ⟶ ((singleFunctor C 0).obj V)⟦-q⟧) :
    let F := singleFunctor C 0
    let H := homologyFunctor C q
    let e := singleFunctorCompHomologyFunctorIso (C := C) q
    let η := (singleFunctors C).shiftIso (-q) q 0 (by omega)
    let μ := shiftFunctorCompIsoId (Plus C) (-q) q (by omega)
    let adj : shiftFunctor (Plus C) (-q) ⊣ shiftFunctor (Plus C) q :=
      (shiftEquiv' (Plus C) (-q) q (by omega)).toAdjunction
    let z := (adj.homEquiv (F.obj U) K) (η.hom.app U ≫ x)
    z ≫ t⟦q⟧' ≫ μ.hom.app (F.obj V) =
      F.map (e.inv.app U ≫ H.map (x ≫ t ≫ η.hom.app V) ≫ e.hom.app V) := by
  intro F H e η μ adj z
  let S := singleFunctor C q
  let a := e.inv.app U ≫ H.map (x ≫ t ≫ η.hom.app V) ≫ e.hom.app V
  have hs : x ≫ t ≫ η.hom.app V = S.map a := by
    apply (ι : Plus C ⥤ DerivedCategory C).map_injective
    apply DerivedCategory.homology_map_injective_of_isGE_of_isLE _ _ q
    change H.map (x ≫ t ≫ η.hom.app V) = H.map (S.map a)
    apply (cancel_mono (e.hom.app V)).mp
    have h : H.map (S.map a) ≫ e.hom.app V = e.hom.app U ≫ a := e.hom.naturality a
    rw [h]
    simp only [a, Iso.hom_inv_id_app_assoc]
  have hv : η.hom.app U ≫ x ≫ t = (F.map a)⟦-q⟧' := by
    apply (cancel_mono (η.hom.app V)).mp
    have h : (F.map a)⟦-q⟧' ≫ η.hom.app V = η.hom.app U ≫ S.map a :=
      η.hom.naturality a
    simpa only [Category.assoc, hs] using h.symm
  let I := F.obj U
  let J := F.obj V
  have hn : (adj.homEquiv I (J⟦-q⟧)) ((η.hom.app U ≫ x) ≫ t) = z ≫ t⟦q⟧' :=
    adj.homEquiv_naturality_right (η.hom.app U ≫ x) t
  have hμ : ((F.map a)⟦-q⟧')⟦q⟧' ≫ μ.hom.app J = μ.hom.app I ≫ F.map a :=
    μ.hom.naturality (F.map a)
  let z' : ShiftedHom I K q := z
  change z' ≫ t⟦q⟧' ≫ μ.hom.app J = F.map a
  have hx : ((η.hom.app U ≫ x) ≫ t) = (F.map a)⟦-q⟧' :=
    (Category.assoc _ _ _).trans hv
  have h₀ : z' ≫ t⟦q⟧' = (adj.homEquiv I (J⟦-q⟧)) ((F.map a)⟦-q⟧') :=
    hn.symm.trans (congrArg (adj.homEquiv I (J⟦-q⟧)) hx)
  calc
    _ = (z' ≫ t⟦q⟧') ≫ μ.hom.app J := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [h₀, adj.homEquiv_unit]
      change (μ.inv.app I ≫ ((F.map a)⟦-q⟧')⟦q⟧') ≫ μ.hom.app J = F.map a
      rw [Category.assoc, hμ, μ.inv_hom_id_app_assoc]

end DerivedCategory.Plus

namespace DerivedCategory.Plus

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- In native shifted Hom, the original mixed trace is the negative boundary
of the same first homology class followed by the same coefficient map. -/
theorem mixedEdge_precomp_topSingle_shiftedTrace
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
    (θ : S.X₁ ⟶ V) (t : ShiftedHom T.obj₁ ((singleFunctor C 0).obj V) (-1 : ℤ))
    (ht : (homologyFunctor C 1).map
      (t ≫ (((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app V).hom) ≫
        (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app V = a ≫ θ) :
    let F := singleFunctor C 0
    let U := F.obj W
    let η := (singleFunctors C).shiftIso (-1) 1 0 (by omega)
    let adj : shiftFunctor (Plus C) (-1 : ℤ) ⊣ shiftFunctor (Plus C) (1 : ℤ) :=
      (shiftEquiv' (Plus C) (-1 : ℤ) 1 (by omega)).toAdjunction
    let z : ShiftedHom U T.obj₃ (1 : ℤ) := adj.homEquiv U T.obj₃ (η.hom.app W ≫ x)
    (z.comp (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) (by omega : 1 + 1 = (2 : ℤ))).comp
        t (by omega) =
      -(F.map j ≫ hS.singleTrianglePlus.mor₃ ≫ (F.map θ)⟦(1 : ℤ)⟧') := by
  intro F U η adj z
  let I := F.obj V
  let μ := shiftFunctorCompIsoId (Plus C) (-1 : ℤ) 1 (by omega)
  let d : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ) := T.mor₃
  let r := d ≫ t⟦(1 : ℤ)⟧' ≫ μ.hom.app I
  let w : ShiftedHom U I (1 : ℤ) :=
    F.map j ≫ hS.singleTrianglePlus.mor₃ ≫ (F.map θ)⟦(1 : ℤ)⟧'
  have h₀ : d.comp t (by omega : (-1 : ℤ) + 1 = 0) = ShiftedHom.mk₀ 0 rfl r :=
    ShiftedHom.comp_neg_eq_mk₀ 1 d t
  have hEdge : η.hom.app W ≫ x ≫ r = -(adj.homEquiv U I).symm w :=
    mixedEdge_precomp_topSingle_trace T hT hS a b c h₁ h₂ x j hx θ t ht
  have hAdj : (adj.homEquiv U I) ((η.hom.app W ≫ x) ≫ r) = z ≫ r⟦(1 : ℤ)⟧' :=
    adj.homEquiv_naturality_right (η.hom.app W ≫ x) r
  change (z.comp d (by omega : 1 + 1 = (2 : ℤ))).comp t (by omega) = -w
  rw [ShiftedHom.comp_assoc z d t (by omega : 1 + 1 = (2 : ℤ))
    (by omega : (-1 : ℤ) + 1 = 0) (by omega : (-1 : ℤ) + 1 + 1 = 1), h₀,
    ShiftedHom.comp_mk₀, ← hAdj, Category.assoc, hEdge]
  change (adj.homAddEquiv U I) (-((adj.homAddEquiv U I).symm w)) = -w
  rw [map_neg, AddEquiv.apply_symm_apply]

end DerivedCategory.Plus
