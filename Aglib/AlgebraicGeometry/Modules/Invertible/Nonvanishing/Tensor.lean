/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Presheaf.SheafificationRestrictionUnit
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# Nonvanishing of the original tensor section

First identify the whole original tensor-frame map against the original
sheafification unit. Its sectionwise value is multiplication of the two
original coefficients. Consequently the nonvanishing open of the actual
pure tensor section is the intersection of the two nonvanishing opens.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The complete original tensor-frame comparison carries the restricted
sheafification unit to the literal tensor of the supplied frame maps. -/
theorem tensorOverTrivialization_unit (X : Scheme.{u})
    (M N : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    PresheafOfModules.Restriction.restrictedSheafificationUnit X.ringCatSheaf U
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val) ≫
      (SheafOfModules.forget (X.ringCatSheaf.over U)).map
        (tensorOverTrivialization X M N U e f).hom =
      (tensorPresheafOverIso X M N U).hom ≫
        PresheafOfModulesOfCommRing.Monoidal.tensorHom e.hom.val f.hom.val ≫
          (leftUnitor (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
            (SheafOfModules.unit (X.ringCatSheaf.over U)).val).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (X.ringCatSheaf.over U).obj)
  let S := PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)
  let F := SheafOfModules.forget (X.ringCatSheaf.over U)
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val
  let Q := SheafOfModules.unit (X.ringCatSheaf.over U)
  let φ : (PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj P ⟶ Q.val :=
    (tensorPresheafOverIso X M N U).hom ≫
      PresheafOfModulesOfCommRing.Monoidal.tensorHom e.hom.val f.hom.val ≫
        (leftUnitor (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
          Q.val).hom
  have he : (tensorOverTrivialization X M N U e f).hom =
      (PresheafOfModules.Restriction.sheafificationOverIso X.ringCatSheaf U P).inv ≫
        S.map φ ≫ adj.counit.app Q := by
    simp only [tensorOverTrivialization, φ, Iso.trans_hom, Iso.symm_hom,
      CategoryTheory.Functor.mapIso_hom, asIso_hom, CategoryTheory.Functor.map_comp, Category.assoc]
    rfl
  rw [he, CategoryTheory.Functor.map_comp, ← Category.assoc,
    PresheafOfModules.Restriction.sheafificationOverIso_inv_unit]
  change adj.unit.app ((PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj P) ≫
    F.map (S.map φ ≫ adj.counit.app Q) = φ
  apply adj.unit_comp_map_eq_iff _ _ |>.mpr
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation of the whole tensor-frame equation gives the product of the
two original local coefficients. -/
theorem tensorOverTrivialization_coefficient (X : Scheme.{u})
    (M N : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (h : V ≤ U) (s : Γ(M, V)) (t : Γ(N, V)) :
    chartSectionEquiv X (tensorSheaf X M N) U (tensorOverTrivialization X M N U e f)
      V h (moduleTensorSection X M N V s t) =
      chartSectionEquiv X M U e V h s * chartSectionEquiv X N U f V h t := by
  have hv := congrArg
    (fun z => z.app (op (Over.mk (homOfLE h))) (s ⊗ₜ[Γ(X, V)] t))
    (tensorOverTrivialization_unit X M N U e f)
  exact hv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The geometric nonvanishing open of the original tensor section is the
intersection of the original two nonvanishing opens. -/
theorem nonvanishingOpen_tensor (X : Scheme.{u}) (L M : LineBundle X)
    (s : Γ(L.val, ⊤)) (t : Γ(M.val, ⊤)) :
    nonvanishingOpen (tensorLineBundle X L M)
        (moduleTensorSection X L.val M.val ⊤ s t) =
      nonvanishingOpen L s ⊓ nonvanishingOpen M t := by
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  obtain ⟨V, hxV, ⟨f⟩⟩ := (isLocallyRankOne_iff_local_unit X M.val).mp M.property x
  let W := U ⊓ V
  let e' := restrictOverUnitIso X L.val (homOfLE (show W ≤ U from inf_le_left)) e
  let f' := restrictOverUnitIso X M.val (homOfLE (show W ≤ V from inf_le_right)) f
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have h := mem_nonvanishingOpen (tensorLineBundle X L M)
    (moduleTensorSection X L.val M.val ⊤ s t) W
    (tensorOverTrivialization X L.val M.val W e' f') x hxW
  have hr : (tensorLineBundle X L M).val.val.map (homOfLE (show W ≤ ⊤ from le_top)).op
      (moduleTensorSection X L.val M.val ⊤ s t) =
      moduleTensorSection X L.val M.val W
        (L.val.val.map (homOfLE (show W ≤ ⊤ from le_top)).op s)
        (M.val.val.map (homOfLE (show W ≤ ⊤ from le_top)).op t) :=
    moduleTensorSection_restrict L.val M.val (homOfLE le_top) s t
  rw [hr] at h
  have hc := tensorOverTrivialization_coefficient X L.val M.val W e' f' le_rfl
    (L.val.val.map (homOfLE (show W ≤ ⊤ from le_top)).op s)
    (M.val.val.map (homOfLE (show W ≤ ⊤ from le_top)).op t)
  dsimp only [tensorLineBundle] at h
  rw [hc, map_mul, IsUnit.mul_iff] at h
  exact h.trans (and_congr (mem_nonvanishingOpen L s W e' x hxW).symm
    (mem_nonvanishingOpen M t W f' x hxW).symm)

end AlgebraicGeometry.Scheme.Modules.Invertible
