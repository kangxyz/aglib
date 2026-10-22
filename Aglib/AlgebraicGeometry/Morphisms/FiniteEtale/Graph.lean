/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Connectedness

/-!
# Graphs in the native finite etale category

These are the native product, graph, and base-change equations extracted from
`ProperResidue.Fullness`. They apply over arbitrary schemes and morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.ProperResidue

universe u

section GraphMaps

variable {Y S : Scheme.{u}} (i : S ⟶ Y)

@[reassoc]
theorem baseChange_map_first {C D : FiniteEtale Y} (j : C ⟶ D) :
    ((baseChange i).map j).hom.left ≫ pullback.fst D.obj.hom i =
      pullback.fst C.obj.hom i ≫ j.hom.left := pullback.lift_fst _ _ _

@[reassoc]
theorem baseChange_map_second {C D : FiniteEtale Y} (j : C ⟶ D) :
    ((baseChange i).map j).hom.left ≫ pullback.snd D.obj.hom i =
      pullback.snd C.obj.hom i := pullback.lift_snd _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem baseChange_map_isPullback {C D : FiniteEtale Y} (j : C ⟶ D) :
    IsPullback ((baseChange i).map j).hom.left (pullback.fst C.obj.hom i)
      (pullback.fst D.obj.hom i) j.hom.left := by
  have ho : IsPullback
      (((baseChange i).map j).hom.left ≫ pullback.snd D.obj.hom i)
      (pullback.fst C.obj.hom i) i (j.hom.left ≫ D.obj.hom) := by
    rw [baseChange_map_second, Over.w j.hom]
    exact (IsPullback.of_hasPullback C.obj.hom i).flip
  exact ho.of_right (baseChange_map_first i j)
    (IsPullback.of_hasPullback D.obj.hom i).flip

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem baseChange_map_range {C D : FiniteEtale Y} (j : C ⟶ D) :
    Set.range ((baseChange i).map j).hom.left =
      pullback.fst D.obj.hom i ⁻¹' Set.range j.hom.left := by
  let h := baseChange_map_isPullback i j
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨pullback.fst C.obj.hom i z, ?_⟩
    exact congrArg (fun a => a z) h.w.symm
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
    refine ⟨h.isoPullback.inv z, ?_⟩
    exact (congrArg (fun a => a z) h.isoPullback_inv_fst).trans hz

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of finite étale `S`-schemes induced by the open immersions `j` and `k`
with equal ranges. -/
def coverIsoOfRangeEq {C D P : FiniteEtale S} (j : C ⟶ P) (k : D ⟶ P)
    [IsOpenImmersion j.hom.left] [IsOpenImmersion k.hom.left]
    (h : Set.range j.hom.left = Set.range k.hom.left) : C ≅ D :=
  ObjectProperty.isoMk _ (Over.isoMk (IsOpenImmersion.isoOfRangeEq j.hom.left k.hom.left h)
    (by rw [← Over.w k.hom, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Over.w]))

theorem coverIsoOfRangeEq_hom {C D P : FiniteEtale S} (j : C ⟶ P) (k : D ⟶ P)
    [IsOpenImmersion j.hom.left] [IsOpenImmersion k.hom.left]
    (h : Set.range j.hom.left = Set.range k.hom.left) :
    (coverIsoOfRangeEq j k h).hom ≫ k = j := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.isoOfRangeEq_hom_fac j.hom.left k.hom.left h

/-- The fiber product of two finite étale `Y`-schemes, viewed as a finite étale `Y`-scheme. -/
abbrev productCover (C D : FiniteEtale Y) : FiniteEtale Y :=
  mk (pullback.fst C.obj.hom D.obj.hom ≫ C.obj.hom)

/-- The first projection from `productCover C D` to `C` over `Y`. -/
def productFirst (C D : FiniteEtale Y) : productCover C D ⟶ C :=
  ObjectProperty.homMk (Over.homMk (pullback.fst C.obj.hom D.obj.hom) rfl)

/-- The second projection from `productCover C D` to `D` over `Y`. -/
def productSecond (C D : FiniteEtale Y) : productCover C D ⟶ D :=
  ObjectProperty.homMk (Over.homMk (pullback.snd C.obj.hom D.obj.hom) pullback.condition.symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scheme morphism from the base change of `C` along `i` to `productCover C D`,
pairing its projection to `C` with `φ` followed by the projection to `D`. -/
def residueGraphBase {C D : FiniteEtale Y}
    (φ : (baseChange i).obj C ⟶ (baseChange i).obj D) :
    ((baseChange i).obj C).obj.left ⟶ (productCover C D).obj.left :=
  pullback.lift (pullback.fst C.obj.hom i)
    (φ.hom.left ≫ pullback.fst D.obj.hom i) (by
      calc
        pullback.fst C.obj.hom i ≫ C.obj.hom = pullback.snd C.obj.hom i ≫ i :=
          pullback.condition
        _ = (φ.hom.left ≫ pullback.snd D.obj.hom i) ≫ i :=
          congrArg (fun h : ((baseChange i).obj C).obj.left ⟶ S => h ≫ i)
            (Over.w φ.hom).symm
        _ = (φ.hom.left ≫ pullback.fst D.obj.hom i) ≫ D.obj.hom := by
          simpa only [Category.assoc] using congrArg (fun h => φ.hom.left ≫ h)
            (pullback.condition (f := D.obj.hom) (g := i)).symm)

theorem residueGraphBase_first {C D : FiniteEtale Y}
    (φ : (baseChange i).obj C ⟶ (baseChange i).obj D) :
    residueGraphBase i φ ≫ (productFirst C D).hom.left = pullback.fst C.obj.hom i :=
  pullback.lift_fst _ _ _

theorem residueGraphBase_second {C D : FiniteEtale Y}
    (φ : (baseChange i).obj C ⟶ (baseChange i).obj D) :
    residueGraphBase i φ ≫ (productSecond C D).hom.left =
      φ.hom.left ≫ pullback.fst D.obj.hom i := pullback.lift_snd _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The graph of `φ` as a morphism to the base change of `productCover C D` along `i`,
in the finite étale category over `S`. -/
def residueGraph {C D : FiniteEtale Y}
    (φ : (baseChange i).obj C ⟶ (baseChange i).obj D) :
    (baseChange i).obj C ⟶ (baseChange i).obj (productCover C D) :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift (residueGraphBase i φ) (pullback.snd C.obj.hom i) (by
      change residueGraphBase i φ ≫ (productFirst C D).hom.left ≫ C.obj.hom = _
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ C.obj.hom) (residueGraphBase_first i φ)).trans
          pullback.condition))) (pullback.lift_snd _ _ _))

theorem residueGraph_base {C D : FiniteEtale Y}
    (φ : (baseChange i).obj C ⟶ (baseChange i).obj D) :
    (residueGraph i φ).hom.left ≫ pullback.fst (productCover C D).obj.hom i =
      residueGraphBase i φ := pullback.lift_fst _ _ _

theorem residueGraph_structure {C D : FiniteEtale Y}
    (φ : (baseChange i).obj C ⟶ (baseChange i).obj D) :
    (residueGraph i φ).hom.left ≫ pullback.snd (productCover C D).obj.hom i =
      pullback.snd C.obj.hom i := pullback.lift_snd _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem residueGraph_first {C D : FiniteEtale Y}
    (φ : (baseChange i).obj C ⟶ (baseChange i).obj D) :
    residueGraph i φ ≫ (baseChange i).map (productFirst C D) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change (residueGraph i φ).hom.left ≫
    ((baseChange i).map (productFirst C D)).hom.left = 𝟙 _
  apply pullback.hom_ext (f := C.obj.hom) (g := i)
  · calc
      _ = (residueGraph i φ).hom.left ≫
          (pullback.fst (productCover C D).obj.hom i ≫ (productFirst C D).hom.left) :=
        (Category.assoc _ _ _).trans (congrArg
          (fun h => (residueGraph i φ).hom.left ≫ h) (baseChange_map_first i (productFirst C D)))
      _ = residueGraphBase i φ ≫ (productFirst C D).hom.left :=
        (Category.assoc _ _ _).symm.trans (congrArg
          (fun h => h ≫ (productFirst C D).hom.left) (residueGraph_base i φ))
      _ = pullback.fst C.obj.hom i := residueGraphBase_first i φ
      _ = _ := (Category.id_comp _).symm
  · calc
      _ = (residueGraph i φ).hom.left ≫ pullback.snd (productCover C D).obj.hom i :=
        (Category.assoc _ _ _).trans (congrArg
          (fun h => (residueGraph i φ).hom.left ≫ h) (baseChange_map_second i (productFirst C D)))
      _ = pullback.snd C.obj.hom i := residueGraph_structure i φ
      _ = _ := (Category.id_comp _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem residueGraph_second {C D : FiniteEtale Y}
    (φ : (baseChange i).obj C ⟶ (baseChange i).obj D) :
    residueGraph i φ ≫ (baseChange i).map (productSecond C D) = φ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change (residueGraph i φ).hom.left ≫
    ((baseChange i).map (productSecond C D)).hom.left = φ.hom.left
  apply pullback.hom_ext (f := D.obj.hom) (g := i)
  · calc
      _ = (residueGraph i φ).hom.left ≫
          (pullback.fst (productCover C D).obj.hom i ≫ (productSecond C D).hom.left) :=
        (Category.assoc _ _ _).trans (congrArg
          (fun h => (residueGraph i φ).hom.left ≫ h) (baseChange_map_first i (productSecond C D)))
      _ = residueGraphBase i φ ≫ (productSecond C D).hom.left :=
        (Category.assoc _ _ _).symm.trans (congrArg
          (fun h => h ≫ (productSecond C D).hom.left) (residueGraph_base i φ))
      _ = _ := residueGraphBase_second i φ
  · calc
      _ = (residueGraph i φ).hom.left ≫ pullback.snd (productCover C D).obj.hom i :=
        (Category.assoc _ _ _).trans (congrArg
          (fun h => (residueGraph i φ).hom.left ≫ h) (baseChange_map_second i (productSecond C D)))
      _ = pullback.snd C.obj.hom i := residueGraph_structure i φ
      _ = φ.hom.left ≫ pullback.snd D.obj.hom i := (Over.w φ.hom).symm

end GraphMaps

end AlgebraicGeometry.Scheme.FiniteEtale.ProperResidue
