/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
/-!
# Restriction and pointwise local bases of vector bundles

These lemmas use the actual Zariski local generating families, retaining their
finite index sets under restriction to smaller opens.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} {M N : X.Modules}

/-- A section over `U` gives the compatible family of all its restrictions. -/
def sectionOver (M : X.Modules) (U : X.Opens) (s : M.val.obj (op U)) :
    (M.over U).sections where
  val V := M.val.presheaf.map V.unop.hom.op s
  property {V W} f := by
    have h := M.val.map_comp_apply V.unop.hom.op f.unop.left.op s
    have hh : V.unop.hom.op ≫ f.unop.left.op = W.unop.hom.op :=
      congrArg Quiver.Hom.op (Over.w f.unop)
    rw [hh] at h
    exact h.symm

@[simp]
theorem sectionOver_top (M : X.Modules) (U : X.Opens) (s : M.val.obj (op U)) :
    (sectionOver M U s).val (op (Over.mk (𝟙 U))) = s := by
  change M.val.presheaf.map (𝟙 (op U)) s = s
  simp

/-- A compatible family on `Over U` is determined by its value on `U`. -/
theorem over_sections_ext (U : X.Opens) (s t : (M.over U).sections)
    (h : s.val (op (Over.mk (𝟙 U))) = t.val (op (Over.mk (𝟙 U)))) : s = t := by
  ext V
  let f : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom (by simp)
  have hs := s.property f.op
  have ht := t.property f.op
  exact hs.symm.trans ((congrArg _ h).trans ht)

@[simp]
theorem sectionOver_eval (U : X.Opens) (s : (M.over U).sections) :
    sectionOver M U (s.val (op (Over.mk (𝟙 U)))) = s :=
  over_sections_ext U _ _ (by simp)

@[simp]
theorem sectionsMap_over_sectionOver (f : M ⟶ N) (U : X.Opens)
    (s : M.val.obj (op U)) :
    SheafOfModules.sectionsMap (f.over U) (sectionOver M U s) =
      sectionOver N U (f.val.app (op U) s) := by
  apply over_sections_ext U
  simp only [sectionOver_top]
  change f.val.app (op U) ((sectionOver M U s).val (op (Over.mk (𝟙 U)))) = _
  rw [sectionOver_top]

/-- Restrict a local generating family to a smaller open, keeping the same
index type. -/
def restrictLocalBasis {U V : X.Opens} (h : V ≤ U)
    (G : (M.over U).GeneratingSections) : (M.over V).GeneratingSections :=
  (G.map (SheafOfModules.overMap X.ringCatSheaf (homOfLE h))
    (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE h)).symm).ofEpi
      ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app M).hom

instance restrictLocalBasis_isFiniteType {U V : X.Opens} (h : V ≤ U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    (restrictLocalBasis h G).IsFiniteType := by
  dsimp [restrictLocalBasis]
  infer_instance

instance restrictLocalBasis_isIso {U V : X.Opens} (h : V ≤ U)
    (G : (M.over U).GeneratingSections) [IsIso G.π] :
    IsIso (restrictLocalBasis h G).π := by
  dsimp [restrictLocalBasis]
  infer_instance

/-- Every point has a finite local basis exactly when the sheaf is finite
locally free in the covering-family definition. -/
theorem finiteLocallyFree_iff_pointwise : IsFiniteLocallyFree X M ↔
    ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ G : (M.over U).GeneratingSections, IsIso G.π ∧ G.IsFiniteType := by
  constructor
  · intro h x
    obtain ⟨q, hq, hf⟩ := h.exists_localBasis
    obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hx⟩ := q.coversTop ⊤ x (by simp)
    exact ⟨q.X i, (leOfHom g) hx, q.generators i, inferInstance, hf.isFiniteType i⟩
  · intro h
    choose U hx G hG hfin using h
    let q : SheafOfModules.LocalGeneratorsData.{u} M := {
      I := X
      X := U
      coversTop := by
        intro V x hxV
        exact ⟨V ⊓ U x, homOfLE inf_le_left,
          ⟨x, ⟨homOfLE inf_le_right⟩⟩, hxV, hx x⟩
      generators := G }
    refine ⟨q, ?_, ?_⟩
    · constructor
      intro i
      exact hG i
    · constructor
      intro i
      exact hfin i

/-- Restricting the generating family restricts each generator as a section. -/
theorem restrictLocalBasis_s_top {U V : X.Opens} (h : V ≤ U) (G : (M.over U).GeneratingSections) (i
  : G.I) :
    ((restrictLocalBasis h G).s i).val (op (Over.mk (𝟙 V))) =
      M.val.map (homOfLE h).op ((G.s i).val (op (Over.mk (𝟙 U)))) := by
  let F := SheafOfModules.overMap X.ringCatSheaf (homOfLE h)
  let η := (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE h)).symm
  let e := (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app M
  change (SheafOfModules.sectionsMap e.hom
    ((F.obj (M.over U)).unitHomEquiv
      (SheafOfModules.ιFree i ≫ ((SheafOfModules.mapFreeIso F G.I η).hom ≫ F.map G.π)))).val
      (op (Over.mk (𝟙 V))) = _
  rw [SheafOfModules.ιFree_mapFreeIso_hom_assoc]
  change (SheafOfModules.sectionsMap e.hom
    ((F.obj (M.over U)).unitHomEquiv
      (F.map (SheafOfModules.ιFree i) ≫ F.map G.π))).val
      (op (Over.mk (𝟙 V))) = _
  rw [← F.map_comp]
  change ((M.over U).unitHomEquiv (SheafOfModules.ιFree i ≫ G.π)).val
    (op (Over.mk (homOfLE h))) = _
  have hG : (M.over U).unitHomEquiv (SheafOfModules.ιFree i ≫ G.π) = G.s i :=
    congrFun ((M.over U).freeHomEquiv.apply_symm_apply G.s) i
  rw [hG]
  exact ((G.s i).property
    (Over.homMk (homOfLE h) (by simp) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op).symm

end AlgebraicGeometry.Scheme.Modules
