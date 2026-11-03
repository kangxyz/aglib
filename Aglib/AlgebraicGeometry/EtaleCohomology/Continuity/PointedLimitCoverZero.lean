/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.PointedTargetRefinement
public import Aglib.CategoryTheory.Over.ChartTails
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCohomologyDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativePullbackCoefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # A whole limit-cover zero descends to an actual pointed target refinement

The original finite-etale cover is descended once. The existing native chart
tail and its actual limit carry the same class to a later stage. The marked
source is transported along the original reconstruction and cone leg. No
finite-presentation hypothesis is placed on that mark, and no normality,
Noetherianity, or closed-point assumption is introduced.

Zero on the whole limit cover is an explicit input. A zero only over a generic
base open does not supply it. This consumes existing continuity, not a new
proof of that theorem or a proof of smooth base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Over.ChartTails

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- An original class zero on an actual pointed limit cover vanishes on a
point-retaining etale refinement of the original target. The standard Ext
realization is retained on the original source, limit, and every stage. -/
theorem exists_pointed_etale_refinement_of_whole_limit_cover_zero
    {I : Type u} [Category.{u} I] [IsCofiltered I] {X P : Scheme.{u}}
    (D : I ⥤ Over X) (c : Cone D)
    (hc : IsLimit ((Over.forget X).mapCone c))
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ i, Etale (D.obj i).hom]
    (Y : FiniteEtale c.pt.left) (y : P ⟶ Y.obj.left) (x : P ⟶ X)
    (hy : y ≫ Y.obj.hom ≫ c.pt.hom = x)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (δ : Sheaf.H.{u + 2} F q)
    (hδ : cohomologyPullback.{u, u + 2, u + 2}
      (Y.obj.hom ≫ c.pt.hom) F q δ = 0) :
    ∃ (V : X.Etale) (v : P ⟶ V.left), v ≫ V.hom = x ∧
      cohomologyPullback.{u, u + 2, u + 2} V.hom F q δ = 0 := by
  obtain ⟨i, Yi, e, _, _, _, _, _, _⟩ :=
    FiniteEtale.LimitDescent.exists_pointed_target_etale_refinement_of_limit_cover
      D c hc Y y x hy
  let E := D ⋙ Over.forget X
  let T := chartTail D i Yi.obj
  let d := nativeChartTailCone D c i Yi.obj
  have hd : IsLimit ((Over.forget X).mapCone d) :=
    nativeChartTailConeIsLimit D c hc i Yi.obj
  let : ∀ j, CompactSpace (E.obj j) := fun j =>
    inferInstanceAs (CompactSpace (D.obj j).left)
  let : ∀ j, QuasiSeparatedSpace (E.obj j) := fun j =>
    inferInstanceAs (QuasiSeparatedSpace (D.obj j).left)
  let : ∀ {j k} (a : j ⟶ k), IsAffineHom (E.map a) := fun {_ _} a =>
    inferInstanceAs (IsAffineHom (D.map a).left)
  let : ∀ j, CompactSpace (T.obj j).left := fun j =>
    inferInstanceAs (CompactSpace ((Scheme.baseChangeDiagram E i Yi.obj.hom).obj j))
  let : ∀ j, QuasiSeparatedSpace (T.obj j).left := fun j =>
    inferInstanceAs (QuasiSeparatedSpace ((Scheme.baseChangeDiagram E i Yi.obj.hom).obj j))
  let : ∀ {j k} (a : j ⟶ k), IsAffineHom (T.map a).left := fun {_ _} a =>
    inferInstanceAs (IsAffineHom ((Scheme.baseChangeDiagram E i Yi.obj.hom).map a))
  have he : e.hom.hom.left ≫ (Y.obj.hom ≫ c.pt.hom) = d.pt.hom := by
    rw [← Category.assoc, Over.w]
    rfl
  have heinv : e.inv.hom.left ≫ d.pt.hom = Y.obj.hom ≫ c.pt.hom := by
    have hi : e.inv.hom.left ≫ e.hom.hom.left = 𝟙 _ :=
      ((FiniteEtale.forgetToScheme c.pt.left).mapIso e).inv_hom_id
    exact (congrArg (fun z => e.inv.hom.left ≫ z) he).symm.trans
      ((Category.assoc e.inv.hom.left e.hom.hom.left (Y.obj.hom ≫ c.pt.hom)).symm.trans
        ((congrArg (fun z => z ≫ (Y.obj.hom ≫ c.pt.hom)) hi).trans (Category.id_comp _)))
  have hzcomp : cohomologyPullback.{u, u + 2, u + 2}
      (e.hom.hom.left ≫ (Y.obj.hom ≫ c.pt.hom)) F q δ = 0 := by
    let α := ((inverseImageComp (Y.obj.hom ≫ c.pt.hom) e.hom.hom.left).app F)
    apply (cohomologyMapIso_bijective α q).injective
    have h := cohomologyPullback_comp.{u, u + 2, u + 2, u + 2}
      (Y.obj.hom ≫ c.pt.hom) e.hom.hom.left F q δ
    exact h.trans ((congrArg (cohomologyPullback e.hom.hom.left
      ((inverseImage (Y.obj.hom ≫ c.pt.hom)).obj F) q) hδ).trans
        ((map_zero _).trans (map_zero _).symm))
  have hz : cohomologyPullback.{u, u + 2, u + 2} d.pt.hom F q δ = 0 :=
    Eq.mp (congrArg (fun z => cohomologyPullback.{u, u + 2, u + 2} z F q δ = 0) he) hzcomp
  let B := (T ⋙ Over.forget X).op
  let : IsConnected (Over i)ᵒᵖ := IsFiltered.isConnected _
  let : ∀ j, CompactSpace (B.obj j).unop := fun j =>
    inferInstanceAs (CompactSpace (T.obj j.unop).left)
  let : ∀ j, QuasiSeparatedSpace (B.obj j).unop := fun j =>
    inferInstanceAs (QuasiSeparatedSpace (T.obj j.unop).left)
  let : ∀ {j k} (a : j ⟶ k), IsAffineHom (B.map a).unop := fun {_ _} a =>
    inferInstanceAs (IsAffineHom (T.map a.unop).left)
  let b := Stalk.relativeCoefficientBaseCone T
  let C := ((Over.forget X).mapCone d).op
  let l : b.pt ⟶ C.pt := d.pt.hom.op
  have hl : ∀ j, b.π.app j ≫ C.ι.app j = l :=
    Stalk.relativeCoefficient_cone_composite T d
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 2}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 2, u + 2, u, u} _
  obtain ⟨j, hj⟩ := Stalk.exists_pullback_eq_zero_of_colimit B b C l hl F q
    (Stalk.isColimitPullbackCohomologyCocone B b C hd.op l hl F q) δ hz
  have hstr : (T.obj j.unop).hom =
      pullback.fst (D.map j.unop.hom).left Yi.obj.hom ≫ (D.obj j.unop.left).hom := by
    change pullback.snd (D.map j.unop.hom).left Yi.obj.hom ≫
      Yi.obj.hom ≫ (D.obj i).hom = _
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w]
  have hstage : Etale (D.obj j.unop.left).hom := ‹∀ i, Etale (D.obj i).hom› _
  let : Etale Yi.obj.hom := inferInstance
  have hprojection : Etale (pullback.fst (D.map j.unop.hom).left Yi.obj.hom) :=
    inferInstance
  let : Etale (T.obj j.unop).hom := by
    rw [hstr]
    exact @AlgebraicGeometry.Etale.etale_comp _ _
      (pullback.fst (D.map j.unop.hom).left Yi.obj.hom) _ (D.obj j.unop.left).hom
      hprojection hstage
  let V : X.Etale := Etale.mk (T.obj j.unop).hom
  let v := y ≫ e.inv.hom.left ≫ (d.π.app j.unop).left
  refine ⟨V, v, ?_, hj⟩
  change (y ≫ e.inv.hom.left ≫ (d.π.app j.unop).left) ≫ (T.obj j.unop).hom = x
  exact (Category.assoc y (e.inv.hom.left ≫ (d.π.app j.unop).left)
    (T.obj j.unop).hom).trans
    ((congrArg (fun z => y ≫ z)
      ((Category.assoc e.inv.hom.left (d.π.app j.unop).left (T.obj j.unop).hom).trans
        ((congrArg (fun z => e.inv.hom.left ≫ z) (Over.w (d.π.app j.unop))).trans
          heinv))).trans hy)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
