/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Modules.Objects
public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation

/-!
# Actual line bundles on affine-transition limits

Finitely presented module descent and eventual local rank one give actual
line-bundle models above any prescribed stage. The original cone projection
recovers the given bundle. A specified lifting property at the stages then
transports through this comparison to the original fibre.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- An actual line bundle descends above any original stage of a qcqs
inverse limit with affine transition maps. -/
theorem exists_lineBundle_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) (L : LineBundle c.pt) :
    ∃ (j : I) (_ : j ⟶ i₀) (N : LineBundle (D.obj j)),
      Nonempty ((pullback (c.π.app j)).obj N.val ≅ L.val) := by
  have : L.val.IsFinitePresentation := lineBundle_isFinitePresentation _ L
  obtain ⟨i, r, M, hM, ⟨e⟩⟩ := exists_model_above_of_isLimit D c hc i₀ L.val
  have : M.IsFinitePresentation := hM
  have hL : IsLocallyRankOne c.pt ((pullback (c.π.app i)).obj M) :=
    isLocallyRankOne_of_iso _ e.symm L.property
  obtain ⟨j, q, hj⟩ := exists_isLocallyRankOne_pullback_above_of_isLimit D c hc i M hL
  refine ⟨j, q ≫ r, ⟨(pullback (D.map q)).obj M, hj⟩, ⟨?_⟩⟩
  exact ((pullbackConeCompIso D c q).app M).symm ≪≫ e

/-- Original stage lifts give a lift of every actual bundle on the specified
limit fibre, retaining its original pullback comparison. -/
theorem exists_lineBundle_lift_of_stage_lifts
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c)
    {K X : Scheme.{u}} (i : K ⟶ X) (e : K ≅ c.pt)
    (h : ∀ j (C : LineBundle (D.obj j)), ∃ W : LineBundle X,
      Nonempty ((pullback i).obj W.val ≅
        (pullback (e.hom ≫ c.π.app j)).obj C.val))
    (L : LineBundle K) :
    ∃ W : LineBundle X, Nonempty ((pullback i).obj W.val ≅ L.val) := by
  classical
  let : Nonempty I := IsCofiltered.nonempty
  obtain ⟨j, _, C, ⟨d⟩⟩ := exists_lineBundle_above_of_isLimit D c hc
    (Classical.arbitrary I) (pullbackLineBundle e.inv L)
  obtain ⟨W, ⟨hW⟩⟩ := h j C
  refine ⟨W, ⟨hW ≪≫ ?_⟩⟩
  exact ((pullbackComp e.hom (c.π.app j)).symm.app C.val) ≪≫
    (pullback e.hom).mapIso d ≪≫ (pullbackComp e.hom e.inv).app L.val ≪≫
      (pullbackCongr e.hom_inv_id).app L.val ≪≫ (pullbackId K).app L.val

end AlgebraicGeometry.Scheme.Modules.Invertible
