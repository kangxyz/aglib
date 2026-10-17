/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Overlap
public import Aglib.RingTheory.Grassmannian.Covering
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The Grassmannian scheme glued from its coordinate charts

The coordinate charts `chartScheme R (e_I)`, indexed by `I : Fin k → Fin n`, are glued along the
overlaps `chartOverlapScheme` with the transition isomorphisms `chartOverlapIso`. Every map in the
gluing data is characterized by the point of the Grassmannian that it classifies, so the gluing
identities hold because all transition maps preserve the classified point. This is the gluing of
Nitsure, arXiv:math/0504590v1, §1, "Construction of Grassmannian", p. 8, over `Spec R`.

## Main definitions

- `AlgebraicGeometry.Grassmannian.glueData R k n`: the `Scheme.GlueData`, with
  `t' = tripleT`, `t_fac = tripleT_fac` and `cocycle` from `tripleTOver_cocycle`.
- `AlgebraicGeometry.Grassmannian.scheme R k n`: the glued scheme; its charts are the open
  immersions `(glueData R k n).ι I` and its structure morphism is `toBase R k n`
  (`ι_toBase`), giving `schemeOver R k n : Over (Spec R)`.

- `AlgebraicGeometry.Grassmannian.comp_chartι_eq_of_point_eq`,
  `point_eq_of_comp_chartι_eq`: maps into charts agree in the glued scheme exactly when they
  classify the same point.
- `AlgebraicGeometry.Grassmannian.chartLocalEquiv`: on every scheme over `Spec R`, maps that
  factor through a coordinate chart correspond to points lying in a coordinate chart.

The whole functor of points of the glued scheme is not yet identified with
`Module.Grassmannian.functor`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

variable {R : CommRingCat.{u}} {k n : ℕ}

instance (x y : Fin k → Fin n → R) : IsOpenImmersion (chartOverlapToChart R x y).left :=
  isOpenImmersion_chartOverlapToChart_left R x y

/-- The pullback of the overlaps of `x` with `y` and with `z`, as a scheme over `Spec R`. -/
abbrev tripleOver (x y z : Fin k → Fin n → R) : Over (Spec R) :=
  Over.mk (pullback.fst (chartOverlapToChart R x y).left (chartOverlapToChart R x z).left ≫
    (chartOverlapScheme R x y).hom)

/-- The first projection of the triple overlap. -/
def tripleFst (x y z : Fin k → Fin n → R) : tripleOver x y z ⟶ chartOverlapScheme R x y :=
  Over.homMk (pullback.fst _ _) rfl

/-- The second projection of the triple overlap. -/
def tripleSnd (x y z : Fin k → Fin n → R) : tripleOver x y z ⟶ chartOverlapScheme R x z :=
  Over.homMk (pullback.snd _ _) (by
    rw [← Over.w (chartOverlapToChart R x z), ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w (chartOverlapToChart R x y)]
    rfl)

theorem tripleFst_comp_eq (x y z : Fin k → Fin n → R) :
    tripleFst x y z ≫ chartOverlapToChart R x y = tripleSnd x y z ≫ chartOverlapToChart R x z :=
  Over.OverMorphism.ext pullback.condition

variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- The point of the Grassmannian classified by the triple overlap. -/
def triplePoint (x y z : Fin k → Fin n → R) :=
  ((chartOverlapRepresentableBy R x y).homEquiv (tripleFst x y z)).1

theorem triplePoint_eq_snd (x y z : Fin k → Fin n → R) :
    triplePoint x y z = ((chartOverlapRepresentableBy R x z).homEquiv (tripleSnd x y z)).1 := by
  rw [triplePoint, ← chartRepresentableBy_homEquiv_comp_chartOverlapToChart,
    ← chartRepresentableBy_homEquiv_comp_chartOverlapToChart, tripleFst_comp_eq]

theorem triplePoint_mem (x y z : Fin k → Fin n → R) :
    triplePoint x y z ∈ Module.Grassmannian.chart _ (Module.Grassmannian.baseChangeTuple _ x) ∧
      triplePoint x y z ∈ Module.Grassmannian.chart _ (Module.Grassmannian.baseChangeTuple _ y) ∧
      triplePoint x y z ∈ Module.Grassmannian.chart _ (Module.Grassmannian.baseChangeTuple _ z) :=
  ⟨((chartOverlapRepresentableBy R x y).homEquiv (tripleFst x y z)).2.1,
    ((chartOverlapRepresentableBy R x y).homEquiv (tripleFst x y z)).2.2,
    (triplePoint_eq_snd x y z) ▸
      ((chartOverlapRepresentableBy R x z).homEquiv (tripleSnd x y z)).2.2⟩

/-- The map from the triple overlap to an overlap classified by the point of the triple overlap. -/
def tripleClassify (x y z : Fin k → Fin n → R) (a b : Fin k → Fin n → R)
    (h : triplePoint x y z ∈
      (Module.Grassmannian.chartFunctor.{u, u, u} R a ⊓ Module.Grassmannian.chartFunctor R b).obj
        (unop ((algΓ R).obj (tripleOver x y z)))) :
    tripleOver x y z ⟶ chartOverlapScheme R a b :=
  (chartOverlapRepresentableBy R a b).homEquiv.symm ⟨triplePoint x y z, h⟩

theorem tripleClassify_homEquiv (x y z a b : Fin k → Fin n → R) (h) :
    ((chartOverlapRepresentableBy R a b).homEquiv (tripleClassify x y z a b h)).1 =
      triplePoint x y z := by
  rw [tripleClassify, Equiv.apply_symm_apply]

theorem tripleClassify_comp_eq (x y z a b c : Fin k → Fin n → R) (h₁ h₂) :
    tripleClassify x y z a b h₁ ≫ chartOverlapToChart R a b =
      tripleClassify x y z a c h₂ ≫ chartOverlapToChart R a c := by
  apply (chartRepresentableBy R a).homEquiv.injective
  apply Subtype.ext
  rw [chartRepresentableBy_homEquiv_comp_chartOverlapToChart,
    chartRepresentableBy_homEquiv_comp_chartOverlapToChart, tripleClassify_homEquiv,
    tripleClassify_homEquiv]

theorem triple_mem_yz (x y z : Fin k → Fin n → R) :
    triplePoint x y z ∈
      (Module.Grassmannian.chartFunctor.{u, u, u} R y ⊓ Module.Grassmannian.chartFunctor R z).obj
        (unop ((algΓ R).obj (tripleOver x y z))) :=
  ⟨(triplePoint_mem x y z).2.1, (triplePoint_mem x y z).2.2⟩

theorem triple_mem_yx (x y z : Fin k → Fin n → R) :
    triplePoint x y z ∈
      (Module.Grassmannian.chartFunctor.{u, u, u} R y ⊓ Module.Grassmannian.chartFunctor R x).obj
        (unop ((algΓ R).obj (tripleOver x y z))) :=
  ⟨(triplePoint_mem x y z).2.1, (triplePoint_mem x y z).1⟩

/-- The gluing map `t'` on triple overlaps. -/
def tripleT (x y z : Fin k → Fin n → R) :
    pullback (chartOverlapToChart R x y).left (chartOverlapToChart R x z).left ⟶
      pullback (chartOverlapToChart R y z).left (chartOverlapToChart R y x).left :=
  pullback.lift (tripleClassify x y z y z (triple_mem_yz x y z)).left
    (tripleClassify x y z y x (triple_mem_yx x y z)).left
    (congrArg CommaMorphism.left (tripleClassify_comp_eq x y z y z x _ _))

/-- The gluing map `t'` as a map of schemes over `Spec R`. -/
def tripleTOver (x y z : Fin k → Fin n → R) : tripleOver x y z ⟶ tripleOver y z x :=
  Over.homMk (tripleT x y z) (by
    change tripleT x y z ≫ pullback.fst _ _ ≫ (chartOverlapScheme R y z).hom = _
    rw [tripleT, ← Category.assoc, pullback.lift_fst]
    exact Over.w (tripleClassify x y z y z (triple_mem_yz x y z)))

theorem tripleTOver_fst (x y z : Fin k → Fin n → R) :
    tripleTOver x y z ≫ tripleFst y z x = tripleClassify x y z y z (triple_mem_yz x y z) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact pullback.lift_fst _ _ _

theorem tripleTOver_snd (x y z : Fin k → Fin n → R) :
    tripleTOver x y z ≫ tripleSnd y z x = tripleClassify x y z y x (triple_mem_yx x y z) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact pullback.lift_snd _ _ _

/-- Pulling back the point of the target triple overlap along `t'` gives the point of the
source. -/
theorem triplePoint_tripleTOver (x y z : Fin k → Fin n → R) :
    (Module.Grassmannian.functor k).map ((algΓ R).map (tripleTOver x y z)).unop
      (triplePoint y z x) = triplePoint x y z := by
  have h := (chartOverlapRepresentableBy R y z).homEquiv_comp (tripleTOver x y z) (tripleFst y z x)
  rw [tripleTOver_fst] at h
  have h' := congrArg Subtype.val h
  rw [tripleClassify_homEquiv] at h'
  exact h'.symm

theorem tripleClassify_yx_eq (x y z : Fin k → Fin n → R) :
    tripleClassify x y z y x (triple_mem_yx x y z) =
      tripleFst x y z ≫ (chartOverlapIso R x y).hom := by
  apply (chartOverlapRepresentableBy R y x).homEquiv.injective
  apply Subtype.ext
  rw [tripleClassify_homEquiv, chartOverlapRepresentableBy_homEquiv_comp_chartOverlapIso]
  rfl

theorem tripleT_fac (x y z : Fin k → Fin n → R) :
    tripleT x y z ≫ pullback.snd _ _ = pullback.fst _ _ ≫ (chartOverlapIso R x y).hom.left := by
  rw [tripleT, pullback.lift_snd, tripleClassify_yx_eq]
  rfl

/-- An endomorphism of the triple overlap that preserves its point is the identity. -/
theorem eq_id_of_triplePoint (x y z : Fin k → Fin n → R) (g : tripleOver x y z ⟶ tripleOver x y z)
    (hg : (Module.Grassmannian.functor k).map ((algΓ R).map g).unop (triplePoint x y z) =
      triplePoint x y z) :
    g = 𝟙 _ := by
  have h1 : g ≫ tripleFst x y z = tripleFst x y z := by
    apply (chartOverlapRepresentableBy R x y).homEquiv.injective
    apply Subtype.ext
    rw [Functor.RepresentableBy.homEquiv_comp]
    exact hg
  have h2 : g ≫ tripleSnd x y z = tripleSnd x y z := by
    apply (chartOverlapRepresentableBy R x z).homEquiv.injective
    apply Subtype.ext
    rw [Functor.RepresentableBy.homEquiv_comp]
    change (Module.Grassmannian.functor k).map ((algΓ R).map g).unop
      ((chartOverlapRepresentableBy R x z).homEquiv (tripleSnd x y z)).1 = _
    rw [← triplePoint_eq_snd]
    exact hg
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa [tripleFst] using congrArg CommaMorphism.left h1
  · simpa [tripleSnd] using congrArg CommaMorphism.left h2

theorem tripleTOver_cocycle (x y z : Fin k → Fin n → R) :
    tripleTOver x y z ≫ tripleTOver y z x ≫ tripleTOver z x y = 𝟙 _ := by
  apply eq_id_of_triplePoint
  simp only [Functor.map_comp, unop_comp, ConcreteCategory.comp_apply, triplePoint_tripleTOver]

variable (R k n) in
/-- The gluing data of the Grassmannian: coordinate charts, their overlaps and the transition
isomorphisms, indexed by the coordinate tuples `Fin k → Fin n`. -/
def glueData : Scheme.GlueData.{u} where
  J := ULift.{u} (Fin k → Fin n)
  U I := (chartScheme R (Module.Grassmannian.coordinateTuple R I.down)).left
  V IJ := (chartOverlapScheme R (Module.Grassmannian.coordinateTuple R IJ.1.down)
    (Module.Grassmannian.coordinateTuple R IJ.2.down)).left
  f I J := (chartOverlapToChart R _ _).left
  f_id I := isIso_chartOverlapToChart_self_left R _
  t I J := (chartOverlapIso R _ _).hom.left
  t_id I := by
    simp [chartOverlapIso, Module.Grassmannian.chartTransitionIso_self]
  t' I J K := tripleT _ _ _
  t_fac I J K := tripleT_fac _ _ _
  cocycle I J K := congrArg CommaMorphism.left (tripleTOver_cocycle _ _ _)
  f_open I J := inferInstance

variable (R k n) in
/-- The Grassmannian scheme of rank-`k` quotients of `R^n`, glued from the coordinate charts. -/
abbrev scheme : Scheme.{u} := (glueData R k n).glued

variable (R k n) in
/-- The structure morphism of the Grassmannian to `Spec R`, glued from those of the charts. -/
def toBase : scheme R k n ⟶ Spec R :=
  Multicoequalizer.desc _ _
    (fun I ↦ (chartScheme R (Module.Grassmannian.coordinateTuple R I.down)).hom) (by
      rintro ⟨I, J⟩
      change (chartOverlapToChart R _ _).left ≫ (chartScheme R _).hom =
        ((chartOverlapIso R _ _).hom.left ≫ (chartOverlapToChart R _ _).left) ≫
          (chartScheme R _).hom
      simp only [Category.assoc, Over.w])

theorem ι_toBase (I : ULift.{u} (Fin k → Fin n)) :
    (glueData R k n).ι I ≫ toBase R k n =
      (chartScheme R (Module.Grassmannian.coordinateTuple R I.down)).hom :=
  Multicoequalizer.π_desc _ _ _ _ _

variable (R k n) in
/-- The Grassmannian as a scheme over `Spec R`. -/
abbrev schemeOver : Over (Spec R) := Over.mk (toBase R k n)

/-- The inclusion of a coordinate chart into the Grassmannian, over `Spec R`. -/
def chartι (I : ULift.{u} (Fin k → Fin n)) :
    chartScheme R (Module.Grassmannian.coordinateTuple R I.down) ⟶ schemeOver R k n :=
  Over.homMk ((glueData R k n).ι I) (ι_toBase I)

/-- Two maps into coordinate charts that classify the same point of the Grassmannian have the
same composite into the glued scheme. -/
theorem comp_chartι_eq_of_point_eq {T : Over (Spec R)} (I J : ULift.{u} (Fin k → Fin n))
    (a : T ⟶ chartScheme R (Module.Grassmannian.coordinateTuple R I.down))
    (b : T ⟶ chartScheme R (Module.Grassmannian.coordinateTuple R J.down))
    (h : ((chartRepresentableBy R _).homEquiv a).1 = ((chartRepresentableBy R _).homEquiv b).1) :
    a ≫ chartι I = b ≫ chartι J := by
  let c : ((algΓ R).leftOp ⋙
      (Module.Grassmannian.chartFunctor.{u, u, u} R
          (Module.Grassmannian.coordinateTuple R I.down) ⊓
        Module.Grassmannian.chartFunctor R
          (Module.Grassmannian.coordinateTuple R J.down)).toFunctor).obj (op T) :=
    ⟨((chartRepresentableBy R _).homEquiv a).1, ((chartRepresentableBy R _).homEquiv a).2,
      h ▸ ((chartRepresentableBy R _).homEquiv b).2⟩
  let g := (chartOverlapRepresentableBy R _ _).homEquiv.symm c
  have hg : ((chartOverlapRepresentableBy R _ _).homEquiv g).1 =
      ((chartRepresentableBy R _).homEquiv a).1 := by
    rw [Equiv.apply_symm_apply]
  have ha : g ≫ chartOverlapToChart R _ _ = a := by
    apply (chartRepresentableBy R _).homEquiv.injective
    apply Subtype.ext
    rw [chartRepresentableBy_homEquiv_comp_chartOverlapToChart, hg]
  have hb : (g ≫ (chartOverlapIso R _ _).hom) ≫ chartOverlapToChart R _ _ = b := by
    apply (chartRepresentableBy R _).homEquiv.injective
    apply Subtype.ext
    rw [chartRepresentableBy_homEquiv_comp_chartOverlapToChart,
      chartOverlapRepresentableBy_homEquiv_comp_chartOverlapIso, hg, h]
  rw [← ha, ← hb]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Category.assoc]
  exact congrArg (g.left ≫ ·) ((glueData R k n).glue_condition I J).symm

/-- Conversely, two maps into coordinate charts with the same composite into the glued scheme
classify the same point of the Grassmannian: the charts meet in their overlap. -/
theorem point_eq_of_comp_chartι_eq {T : Over (Spec R)} (I J : ULift.{u} (Fin k → Fin n))
    (a : T ⟶ chartScheme R (Module.Grassmannian.coordinateTuple R I.down))
    (b : T ⟶ chartScheme R (Module.Grassmannian.coordinateTuple R J.down))
    (h : a ≫ chartι I = b ≫ chartι J) :
    ((chartRepresentableBy R _).homEquiv a).1 = ((chartRepresentableBy R _).homEquiv b).1 := by
  have hl : a.left ≫ (glueData R k n).ι I = b.left ≫ (glueData R k n).ι J :=
    congrArg CommaMorphism.left h
  obtain ⟨g, hg1, hg2⟩ :=
    PullbackCone.IsLimit.lift' ((glueData R k n).vPullbackConeIsLimit I J) a.left b.left hl
  let g' : T.left ⟶ (chartOverlapScheme R (Module.Grassmannian.coordinateTuple R I.down)
      (Module.Grassmannian.coordinateTuple R J.down)).left := g
  have hg1' : g' ≫ (chartOverlapToChart R _ _).left = a.left := hg1
  have hg2' : g' ≫ (chartOverlapIso R _ _).hom.left ≫ (chartOverlapToChart R _ _).left =
      b.left := hg2
  let gO : T ⟶ chartOverlapScheme R (Module.Grassmannian.coordinateTuple R I.down)
      (Module.Grassmannian.coordinateTuple R J.down) :=
    Over.homMk g' (by
      rw [← Over.w (chartOverlapToChart R _ _), ← Category.assoc, hg1']
      exact Over.w a)
  have ha : gO ≫ chartOverlapToChart R _ _ = a := Over.OverMorphism.ext hg1'
  have hb : (gO ≫ (chartOverlapIso R _ _).hom) ≫ chartOverlapToChart R _ _ = b := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, Category.assoc]
    exact hg2'
  rw [← ha, ← hb, chartRepresentableBy_homEquiv_comp_chartOverlapToChart,
    chartRepresentableBy_homEquiv_comp_chartOverlapToChart,
    chartOverlapRepresentableBy_homEquiv_comp_chartOverlapIso]

/-- A point of `G(k, Γ(T, ⊤) ⊗[R] R^n; Γ(T, ⊤))` lying in some coordinate chart. -/
def ChartLocalPoint (T : Over (Spec R)) :=
  {N : (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).obj
      (unop ((algΓ R).obj T)) //
    ∃ I : ULift.{u} (Fin k → Fin n), N ∈ (Module.Grassmannian.chartFunctor.{u, u, u} R
      (Module.Grassmannian.coordinateTuple R I.down)).obj (unop ((algΓ R).obj T))}

/-- A map into the glued scheme that factors through some coordinate chart. -/
def ChartLocalHom (T : Over (Spec R)) :=
  {g : T ⟶ schemeOver R k n // ∃ (I : ULift.{u} (Fin k → Fin n))
    (a : T ⟶ chartScheme R (Module.Grassmannian.coordinateTuple R I.down)), g = a ≫ chartι I}

/-- The point classified by a map that factors through a coordinate chart. -/
def ChartLocalHom.point {T : Over (Spec R)} (g : ChartLocalHom (k := k) (n := n) T) :
    (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).obj
      (unop ((algΓ R).obj T)) :=
  ((chartRepresentableBy R _).homEquiv g.2.choose_spec.choose).1

theorem ChartLocalHom.point_mem {T : Over (Spec R)} (g : ChartLocalHom (k := k) (n := n) T) :
    g.point ∈ (Module.Grassmannian.chartFunctor.{u, u, u} R
      (Module.Grassmannian.coordinateTuple R g.2.choose.down)).obj (unop ((algΓ R).obj T)) :=
  ((chartRepresentableBy R _).homEquiv g.2.choose_spec.choose).2

theorem ChartLocalHom.point_eq {T : Over (Spec R)} (g : ChartLocalHom (k := k) (n := n) T)
    {I : ULift.{u} (Fin k → Fin n)}
    (a : T ⟶ chartScheme R (Module.Grassmannian.coordinateTuple R I.down))
    (h : g.1 = a ≫ chartι I) : g.point = ((chartRepresentableBy R _).homEquiv a).1 :=
  point_eq_of_comp_chartι_eq _ _ _ _ (g.2.choose_spec.choose_spec.symm.trans h)

/-- The chart-local point classified by a chart-local map. -/
def ChartLocalHom.toPoint {T : Over (Spec R)} (g : ChartLocalHom (k := k) (n := n) T) :
    ChartLocalPoint (k := k) (n := n) T :=
  ⟨g.point, g.2.choose, g.point_mem⟩

/-- The chart-local map classifying a chart-local point. -/
def ChartLocalPoint.toHom {T : Over (Spec R)} (N : ChartLocalPoint (k := k) (n := n) T) :
    ChartLocalHom (k := k) (n := n) T :=
  ⟨(chartRepresentableBy R _).homEquiv.symm ⟨N.1, N.2.choose_spec⟩ ≫ chartι N.2.choose,
    N.2.choose, _, rfl⟩

theorem ChartLocalPoint.toHom_val {T : Over (Spec R)} (N : ChartLocalPoint (k := k) (n := n) T) :
    N.toHom.1 =
      (chartRepresentableBy R _).homEquiv.symm ⟨N.1, N.2.choose_spec⟩ ≫ chartι N.2.choose :=
  rfl

theorem ChartLocalHom.toPoint_val {T : Over (Spec R)} (g : ChartLocalHom (k := k) (n := n) T) :
    g.toPoint.1 = g.point :=
  rfl

theorem ChartLocalHom.toPoint_val_eq {T : Over (Spec R)}
    (g : ChartLocalHom (k := k) (n := n) T) :
    g.toPoint.1 = ((chartRepresentableBy R _).homEquiv g.2.choose_spec.choose).1 :=
  rfl

theorem ChartLocalHom.toHom_toPoint {T : Over (Spec R)} (g : ChartLocalHom (k := k) (n := n) T) :
    g.toPoint.toHom = g := by
  apply Subtype.ext
  have h1 : ((chartRepresentableBy R _).homEquiv ((chartRepresentableBy R _).homEquiv.symm
      ⟨g.toPoint.1, g.toPoint.2.choose_spec⟩)).1 = g.toPoint.1 :=
    congrArg Subtype.val ((chartRepresentableBy R _).homEquiv.apply_symm_apply _)
  rw [ChartLocalPoint.toHom_val, comp_chartι_eq_of_point_eq g.toPoint.2.choose g.2.choose _
    g.2.choose_spec.choose (h1.trans (ChartLocalHom.toPoint_val_eq g))]
  exact g.2.choose_spec.choose_spec.symm

theorem ChartLocalPoint.toPoint_toHom {T : Over (Spec R)}
    (N : ChartLocalPoint (k := k) (n := n) T) : N.toHom.toPoint = N := by
  apply Subtype.ext
  rw [ChartLocalHom.toPoint_val]
  exact (ChartLocalHom.point_eq _ _ (ChartLocalPoint.toHom_val N)).trans
    (congrArg Subtype.val ((chartRepresentableBy R _).homEquiv.apply_symm_apply _))

/-- The glued scheme represents the chart-local part of the Grassmannian functor on all schemes
over `Spec R`: maps factoring through a coordinate chart are the points lying in a coordinate
chart. -/
def chartLocalEquiv (T : Over (Spec R)) :
    ChartLocalHom (k := k) (n := n) T ≃ ChartLocalPoint (k := k) (n := n) T where
  toFun := ChartLocalHom.toPoint
  invFun := ChartLocalPoint.toHom
  left_inv := ChartLocalHom.toHom_toPoint
  right_inv := ChartLocalPoint.toPoint_toHom

end AlgebraicGeometry.Grassmannian
