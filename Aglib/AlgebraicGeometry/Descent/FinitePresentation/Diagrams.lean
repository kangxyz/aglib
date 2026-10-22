/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Common stages for finite scheme data

The base-change diagram below consists of the actual pullbacks of one
scheme at a fixed stage. Its limit is the actual pullback to the limit of
the bases. Finite families of maps and finite families of equations can
then be placed at a common stage using Mathlib's Hom-limit theorems.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I]

/-- The actual base changes of a scheme at stage `i`, indexed by arrows into
`i`. Its object at `j` is `pullback (D.map j.hom) f`. -/
def baseChangeDiagram (D : I ⥤ Scheme.{u}) (i : I) {X : Scheme.{u}}
    (f : X ⟶ D.obj i) : Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback f ⋙ Over.forget X

/-- The canonical cone on the actual base-change diagram. Its point is
`pullback (c.π.app i) f`. -/
def baseChangeCone (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) : Cone (baseChangeDiagram D i f) :=
  (Over.pullback f ⋙ Over.forget X).mapCone ((Over.conePost D i).obj c)

/-- Base change of a cofiltered limit is the limit of the actual stage
pullbacks. This constructs the source system needed by Hom descent. -/
def isLimitBaseChangeCone [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) (i : I) {X : Scheme.{u}} (f : X ⟶ D.obj i) :
    IsLimit (baseChangeCone D c i f) :=
  isLimitOfPreserves (Over.pullback f ⋙ Over.forget X) (Over.isLimitConePost i hc)

instance baseChangeDiagram_isAffineHom (D : I ⥤ Scheme.{u}) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [∀ {j k} (g : j ⟶ k), IsAffineHom (D.map g)]
    {j k : Over i} (g : j ⟶ k) :
    IsAffineHom ((baseChangeDiagram D i f).map g) :=
  MorphismProperty.overPullbackMap (P := @IsAffineHom) f ((Over.post D).map g)
    (inferInstanceAs (IsAffineHom (D.map g.left)))

instance baseChangeDiagram_compactSpace (D : I ⥤ Scheme.{u}) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) [QuasiCompact f]
    [∀ j, CompactSpace (D.obj j)] (j : Over i) :
    CompactSpace ((baseChangeDiagram D i f).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map j.hom) f)

instance baseChangeDiagram_quasiSeparatedSpace (D : I ⥤ Scheme.{u}) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) [QuasiSeparated f]
    [∀ j, QuasiSeparatedSpace (D.obj j)] (j : Over i) :
    QuasiSeparatedSpace ((baseChangeDiagram D i f).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map j.hom) f)

/-- A morphism between actual limit base changes descends to an actual morphism
between base changes at one later stage, with its base triangle and comparison. -/
lemma exists_hom_between_baseChanges_of_isLimit [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ D.obj i) (g : Y ⟶ D.obj i)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation g]
    (a : pullback (c.π.app i) f ⟶ pullback (c.π.app i) g)
    (ha : a ≫ pullback.fst (c.π.app i) g = pullback.fst (c.π.app i) f) :
    ∃ (j : Over i) (b : (baseChangeDiagram D i f).obj j ⟶
        (baseChangeDiagram D i g).obj j),
      b ≫ pullback.fst (D.map j.hom) g = pullback.fst (D.map j.hom) f ∧
      (baseChangeCone D c i f).π.app j ≫ b =
        a ≫ (baseChangeCone D c i g).π.app j := by
  let t : baseChangeDiagram D i f ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := pullback.snd (D.map j.hom) f ≫ f
      naturality {j k} q := by
        simp [baseChangeDiagram, Functor.comp_map, Over.forget_map, Over.pullback_map_left] }
  have hbase : pullback.snd (c.π.app i) f ≫ f =
      a ≫ pullback.snd (c.π.app i) g ≫ g := by
    calc
      _ = pullback.fst (c.π.app i) f ≫ c.π.app i := pullback.condition.symm
      _ = a ≫ pullback.fst (c.π.app i) g ≫ c.π.app i := by
        rw [← Category.assoc, ha]
      _ = _ := by rw [pullback.condition]
  obtain ⟨j, b, hb, hb'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D i f) t g (baseChangeCone D c i f)
    (isLimitBaseChangeCone D c hc i f) (a ≫ pullback.snd (c.π.app i) g) (by
      ext j
      simpa [t, baseChangeCone, baseChangeDiagram, Functor.comp_map, Over.forget_map,
        Over.pullback_map_left, Category.assoc] using hbase)
  let b' : (baseChangeDiagram D i f).obj j ⟶ (baseChangeDiagram D i g).obj j :=
    pullback.lift (pullback.fst (D.map j.hom) f) b (by
      rw [hb']
      exact pullback.condition)
  refine ⟨j, b', by simp [b'], ?_⟩
  apply pullback.hom_ext
  · simp [b', baseChangeCone, baseChangeDiagram, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left, Category.assoc, reassoc_of% ha]
  · simpa [b', baseChangeCone, baseChangeDiagram, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left, Category.assoc] using hb

section FiniteFamilies

variable [IsCofiltered I] {J : Type v} [Finite J]
  (D : J → I ⥤ Scheme.{u}) {S X : J → Scheme.{u}}
  (t : ∀ j, D j ⟶ (Functor.const I).obj (S j)) (f : ∀ j, X j ⟶ S j)
  (c : ∀ j, Cone (D j)) (hc : ∀ j, IsLimit (c j))
  [∀ j, ∀ {i k} (g : i ⟶ k), IsAffineHom ((D j).map g)]
  [∀ j i, CompactSpace ((D j).obj i)]

include hc

/-- A finite family of morphisms from cofiltered limits factors at one
common stage. Each target is locally of finite presentation, and each
source system consists of qcqs schemes with affine transition maps. All
structural triangles are retained. -/
lemma exists_common_stage_factorizations_of_locallyOfFinitePresentation
    [∀ j, LocallyOfFinitePresentation (f j)]
    [∀ j i, QuasiSeparatedSpace ((D j).obj i)]
    (a : ∀ j, (c j).pt ⟶ X j)
    (ha : ∀ j, (c j).π ≫ t j = (Functor.const I).map (a j ≫ f j)) :
    ∃ i : I, ∀ j, ∃ g : (D j).obj i ⟶ X j,
      (c j).π.app i ≫ g = a j ∧ g ≫ f j = (t j).app i := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose i g hg hg' using fun j ↦
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (D j) (t j) (f j) (c j) (hc j) (a j) (ha j)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let q (j : J) : k ⟶ i j := (hk (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨k, fun j ↦ ⟨(D j).map (q j) ≫ g j, ?_, ?_⟩⟩
  · rw [← Category.assoc, (c j).w, hg]
  · rw [Category.assoc, hg']
    simp

/-- Finitely many equations between stage morphisms which hold at the
limit hold after one common transition. Local finite type suffices for
the targets; the sources need only be quasi-compact. -/
lemma exists_common_stage_equalities_of_locallyOfFiniteType
    [∀ j, LocallyOfFiniteType (f j)] {i : I}
    (a b : ∀ j, (D j).obj i ⟶ X j)
    (ha : ∀ j, (t j).app i = a j ≫ f j)
    (hb : ∀ j, (t j).app i = b j ≫ f j)
    (hab : ∀ j, (c j).π.app i ≫ a j = (c j).π.app i ≫ b j) :
    ∃ (k : I) (q : k ⟶ i),
      ∀ j, (D j).map q ≫ a j = (D j).map q ≫ b j := by
  choose k q hq using fun j ↦
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (D j) (t j) (f j) (c j) (hc j) (a j) (b j) (ha j) (hb j) (hab j)
  obtain ⟨l, q₀, q', hq'⟩ := IsCofiltered.wideCospan q
  refine ⟨l, q₀, fun j ↦ ?_⟩
  rw [← hq' j, (D j).map_comp]
  simpa only [Category.assoc] using congrArg ((D j).map (q' j) ≫ ·) (hq j)

end FiniteFamilies

end AlgebraicGeometry.Scheme
