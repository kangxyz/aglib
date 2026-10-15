/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.AffinePullback
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.Restriction
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections

/-! # Original section tensor maps under open base change

The scalar section comparison commutes with the original open restriction and
cartesian coefficient comparison. The equation is proved on the actual unit
pure tensors and retains the original restriction maps on sections.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {V Y U X : Scheme.{u}}
  (a : V ⟶ Y) (b : V ⟶ U) (p : Y ⟶ X) (j : U ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b p j)
  {A B : Type u} [CommRing A] [CommRing B]
  (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(Y, ⊤)) (σ : A →+* B)
  (hσ : p.appTop.hom.comp α = β.comp σ)

omit [IsOpenImmersion a] [IsOpenImmersion j] in
/-- Restricting an actual commuting square preserves the displayed structural ring maps. -/
theorem moduleSectionsOpenSquare_scalars
    (hσ : p.appTop.hom.comp α = β.comp σ) (w : a ≫ p = b ≫ j) :
    b.appTop.hom.comp (j.appTop.hom.comp α) = (a.appTop.hom.comp β).comp σ := by
  ext r
  have hw := congrArg (fun z : V ⟶ X => z.appTop) w
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hw
  have hr := congrArg (fun z : Γ(X, ⊤) ⟶ Γ(V, ⊤) => z (α r)) hw
  change a.appTop (p.appTop (α r)) = b.appTop (j.appTop (α r)) at hr
  change b.appTop (j.appTop (α r)) = a.appTop (β (σ r))
  rw [← hr, show p.appTop (α r) = β (σ r) from DFunLike.congr_fun hσ r]

/-- The original target sections on the inverse-image open, identified with its open restriction. -/
def moduleSectionsPullbackRestrictionIso (N : Y.Modules) :
    (moduleSectionsPresheaf Y β N).obj (op (p ⁻¹ᵁ j.opensRange)) ≅
      (moduleSectionsPresheaf V (a.appTop.hom.comp β) (N.restrict a)).obj (op ⊤) :=
  (moduleSectionsPresheaf Y β N).mapIso
      (eqToIso (congrArg op (Scheme.Modules.opensRange_of_isPullback a b p j h).symm)) ≪≫
    moduleSectionsRestrictionIso a β N

/-- The target identification is the original presheaf transport along the actual open equality. -/
theorem moduleSectionsPullbackRestrictionIso_hom_apply (N : Y.Modules)
    (m : (moduleSectionsPresheaf Y β N).obj (op (p ⁻¹ᵁ j.opensRange))) :
    (moduleSectionsPullbackRestrictionIso a b p j h β N).hom m =
      N.presheaf.map (eqToHom (a.image_top_eq_opensRange.trans
        (Scheme.Modules.opensRange_of_isPullback a b p j h))).op m := by
  change N.presheaf.obj (op (p ⁻¹ᵁ j.opensRange)) at m
  change N.presheaf.map _ (N.presheaf.map _ m) = _
  let i := eqToIso (congrArg op (Scheme.Modules.opensRange_of_isPullback a b p j h).symm)
  let k := (eqToIso a.image_top_eq_opensRange.symm).op
  have hik : i.hom ≫ k.inv = (eqToHom (a.image_top_eq_opensRange.trans
      (Scheme.Modules.opensRange_of_isPullback a b p j h))).op := Subsingleton.elim _ _
  have hc := ConcreteCategory.congr_hom (N.presheaf.map_comp i.hom k.inv) m
  rw [hik] at hc
  exact hc.symm

set_option maxRecDepth 2000 in
/-- The original section tensor map is compatible with the actual cartesian open coefficient map. -/
theorem moduleSectionsTensorMapAlong_restriction {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) :
    (moduleSectionsTensorMapAlong p α β σ hσ φ).app (op j.opensRange) ≫
        (moduleSectionsPullbackRestrictionIso a b p j h β N).hom =
      (ModuleCat.extendScalars σ).map (moduleSectionsRestrictionIso j α M).hom ≫
        (moduleSectionsTensorMapAlong b (j.appTop.hom.comp α) (a.appTop.hom.comp β) σ
          (moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w)
          ((Scheme.Modules.restrictFunctor j).map φ ≫
            (Scheme.Modules.cartesianOpenBaseChange a b p j h).hom.app N)).app (op ⊤) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (moduleSectionsPullbackRestrictionIso a b p j h β N).hom
      ((moduleSectionsTensorMapAlong p α β σ hσ φ).app (op j.opensRange)
        ((1 : B) ⊗ₜ[A,σ] m)) = _
  erw [moduleSectionsTensorMapAlong_one_tmul p α β σ hσ φ j.opensRange m]
  change (moduleSectionsPullbackRestrictionIso a b p j h β N).hom (φ.app j.opensRange m) =
    (moduleSectionsTensorMapAlong b (j.appTop.hom.comp α) (a.appTop.hom.comp β) σ
      (moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w)
      ((Scheme.Modules.restrictFunctor j).map φ ≫
        (Scheme.Modules.cartesianOpenBaseChange a b p j h).hom.app N)).app (op ⊤)
      ((1 : B) ⊗ₜ[A,σ] ((moduleSectionsRestrictionIso j α M).hom m))
  erw [moduleSectionsTensorMapAlong_one_tmul]
  rw [moduleSectionsPullbackRestrictionIso_hom_apply]
  change N.presheaf.map _ (φ.app j.opensRange m) =
    (((Scheme.Modules.cartesianOpenBaseChange a b p j h).hom.app N).app ⊤)
      (φ.app (j ''ᵁ ⊤) (M.presheaf.map (eqToHom j.image_top_eq_opensRange).op m))
  rw [Scheme.Modules.cartesianOpenBaseChange_hom_app]
  have hn := congrArg (fun z => z m)
    (φ.mapPresheaf.naturality (eqToHom j.image_top_eq_opensRange).op)
  change φ.app (j ''ᵁ ⊤) (M.presheaf.map (eqToHom j.image_top_eq_opensRange).op m) =
    N.presheaf.map ((Opens.map p.base).map (eqToHom j.image_top_eq_opensRange)).op
      (φ.app j.opensRange m) at hn
  rw [hn]
  exact ConcreteCategory.congr_hom (N.presheaf.map_comp
    ((Opens.map p.base).map (eqToHom j.image_top_eq_opensRange)).op
    (eqToHom (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h.flip ⊤)).op)
    (φ.app j.opensRange m)

include h in
/-- On an affine cartesian open chart, an actual structural-ring pushout makes the original
geometric-unit section tensor map invertible. -/
theorem moduleSectionsTensorComparison_isIso_app_of_isAffine
    [IsAffine U] [IsAffine V]
    (hpush : IsPushout (CommRingCat.ofHom (j.appTop.hom.comp α)) (CommRingCat.ofHom σ)
      b.appTop (CommRingCat.ofHom (a.appTop.hom.comp β)))
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((moduleSectionsTensorComparison p α β σ hσ M).app (op j.opensRange)) := by
  let μ := moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w
  let η := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let e := (Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M
  let L := (moduleSectionsTensorMapAlong b (j.appTop.hom.comp α)
    (a.appTop.hom.comp β) σ μ
    ((Scheme.Modules.restrictFunctor j).map η ≫
      (Scheme.Modules.cartesianOpenBaseChange a b p j h).hom.app
        ((Scheme.Modules.pullback p).obj M))).app (op ⊤)
  have hL : IsIso L := by
    dsimp only [L, η]
    rw [Scheme.Modules.cartesianOpenBaseChange_pullback_unit a b p j h M]
    rw [moduleSectionsTensorMapAlong_comp_app b (j.appTop.hom.comp α)
      (a.appTop.hom.comp β) σ μ
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)) e (op ⊤)]
    have := moduleSectionsTensorComparison_top_isIso b (j.appTop.hom.comp α)
      (a.appTop.hom.comp β) σ μ hpush (M.restrict j)
    change IsIso ((moduleSectionsTensorComparison b (j.appTop.hom.comp α)
      (a.appTop.hom.comp β) σ μ (M.restrict j)).app (op ⊤) ≫
        ((moduleSectionsPresheafFunctor V (a.appTop.hom.comp β)).map e).app
          (op (b ⁻¹ᵁ (⊤ : U.Opens))))
    infer_instance
  have H := moduleSectionsTensorMapAlong_restriction a b p j h α β σ hσ η
  have : IsIso ((moduleSectionsTensorMapAlong p α β σ hσ η).app (op j.opensRange) ≫
      (moduleSectionsPullbackRestrictionIso a b p j h β
        ((Scheme.Modules.pullback p).obj M)).hom) := by
    rw [H]
    change IsIso ((ModuleCat.extendScalars σ).map (moduleSectionsRestrictionIso j α M).hom ≫ L)
    infer_instance
  change IsIso ((moduleSectionsTensorMapAlong p α β σ hσ η).app (op j.opensRange))
  exact IsIso.of_isIso_comp_right _
    (moduleSectionsPullbackRestrictionIso a b p j h β ((Scheme.Modules.pullback p).obj M)).hom

end AlgebraicGeometry.Scheme.Cohomology
