/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine source frames subordinate to affine target charts

An arbitrary scheme morphism and a fixed invertible source module admit an
actual affine source cover whose charts factor through affine target opens
and trivialize the pullback of that same source module. The coordinate maps
are the original `appLE` maps. No finite-cover, row-compatibility or
chart-comparison premise is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation

private theorem exists_affine_frame_neighborhood
    {W X : Scheme.{u}} (f : W ⟶ X) (D : W.Modules)
    (hD : IsLocallyRankOne W D) (w : W) :
    ∃ (V : X.affineOpens) (U : W.affineOpens), w ∈ U.val ∧
      U.val ≤ f ⁻¹ᵁ V.val ∧
        Nonempty ((Modules.pullback U.property.fromSpec).obj D ≅
          SheafOfModules.unit (Spec Γ(W, U.val)).ringCatSheaf) := by
  obtain ⟨V, hV, hfwV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f w ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨T, hwT, ⟨eT⟩⟩ := (isLocallyRankOne_iff_local_unit W D).mp hD w
  obtain ⟨U, hU, hwU, hUTV⟩ := exists_isAffineOpen_mem_and_subset
    (show w ∈ T ⊓ f ⁻¹ᵁ V from ⟨hwT, hfwV⟩)
  have hUT : U ≤ T := hUTV.trans inf_le_left
  have hUV : U ≤ f ⁻¹ᵁ V := hUTV.trans inf_le_right
  let eU : D.over U ≅ SheafOfModules.unit (W.ringCatSheaf.over U) :=
    restrictOverUnitIso W D (homOfLE hUT) eT
  let eR : (Modules.pullback U.ι).obj D ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((restrictFunctorIsoPullback U.ι).app D).symm ≪≫
      ((overFunctorEquiv U).app D).symm ≪≫
        (overEquiv U).functor.mapIso eU ≪≫ overUnitIso U
  let eSpec : (Modules.pullback hU.fromSpec).obj D ≅
      SheafOfModules.unit (Spec Γ(W, U)).ringCatSheaf := by
    change (Modules.pullback (hU.isoSpec.inv ≫ U.ι)).obj D ≅ _
    exact ((pullbackComp hU.isoSpec.inv U.ι).app D).symm ≪≫
      (Modules.pullback hU.isoSpec.inv).mapIso eR ≪≫ pullbackUnitIso hU.isoSpec.inv
  exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hwU, hUV, ⟨eSpec⟩⟩

/-- An arbitrary morphism and an actual invertible source module admit an
actual affine source cover with affine target charts, literal coordinate
ring maps, commuting triangles, and native frames of the same pulled module.
No compactness or finiteness hypothesis is imposed. -/
theorem exists_affine_frame_cover
    {W X : Scheme.{u}} (f : W ⟶ X) (D : W.Modules)
    (hD : IsLocallyRankOne W D) :
    ∃ (𝒰 : Scheme.AffineOpenCover.{u, u} W) (V : 𝒰.I₀ → X.affineOpens)
      (φ : ∀ i, Γ(X, (V i).val) ⟶ 𝒰.X i)
      (_e : ∀ i, (Modules.pullback (𝒰.f i)).obj D ≅
        SheafOfModules.unit (Spec (𝒰.X i)).ringCatSheaf),
      ∀ i, Spec.map (φ i) ≫ (V i).property.fromSpec = 𝒰.f i ≫ f := by
  classical
  choose V U hw hUV he using exists_affine_frame_neighborhood f D hD
  have hcover : IsOpenCover (fun w : W => (U w).val) := by
    apply top_le_iff.mp
    intro w _
    exact Opens.mem_iSup.mpr ⟨w, hw w⟩
  let 𝒰 : Scheme.AffineOpenCover.{u, u} W := AffineOpenCover.ofIsOpenCover
    (fun w : W => (U w).val) hcover (fun w => (U w).property)
  refine ⟨𝒰, V, (fun i => f.appLE (V i).val (U i).val (hUV i)),
    (fun i => Classical.choice (he i)), ?_⟩
  intro i
  exact (V i).property.SpecMap_appLE_fromSpec f (U i).property (hUV i)

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation
