/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyPushforward
public import Aglib.AlgebraicGeometry.Modules.Linear

/-!
# Retaining actual coefficient actions under the Rees comparison

Direct-image comparison commutes with every original coefficient morphism,
including multiplication by global functions on the geometric Rees space.
Together with a sectionwise homogeneous square this identifies the actual
homogeneous action on original cohomology, without choosing a new action.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The original direct-image cohomology map is natural in the original coefficient map. -/
theorem moduleCohomologyPushforwardMap_naturality {G G' : Y.Modules}
    (ψ : G ⟶ G') (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X ((Scheme.Modules.pushforward p).obj G)) q) :
    moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G')) q
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map
        ((Scheme.Modules.pushforward p).map ψ)) q x) =
    Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ) q
      (moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q x) := by
  let φ := (SheafOfModules.toSheaf X.ringCatSheaf).map
    ((Scheme.Modules.pushforward p).map ψ)
  let χ := (SheafOfModules.toSheaf Y.ringCatSheaf).map ψ
  have h : φ ≫ ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (𝟙 ((Scheme.Modules.pushforward p).obj G')) ≫
        (modulePushforwardAddSheafIso p G').hom) =
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (𝟙 ((Scheme.Modules.pushforward p).obj G)) ≫
        (modulePushforwardAddSheafIso p G).hom) ≫ (zariskiPushforward p).map χ := by
    rw [(SheafOfModules.toSheaf.{u} X.ringCatSheaf).map_id,
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map_id]
    simp only [modulePushforwardAddSheafIso, Iso.refl_hom,
      Category.id_comp, Category.comp_id]
    rfl
  have h' := congrArg
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv _ _).symm) h
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm] at h'
  exact zariskiCohomologyMap_map p _ _ φ χ h' q x

/-- Forgetting actual coefficient multiplication gives the structural additive scalar map. -/
theorem globalScalarEndomorphism_toSheaf (G : Y.Modules) (a : Γ(Y, ⊤)) :
    (SheafOfModules.toSheaf Y.ringCatSheaf).map
      (Scheme.Modules.globalScalarEndomorphism Y G a) = moduleScalarOfGlobal Y G a := by
  ext U x
  exact Scheme.Modules.globalScalarEndomorphism_app Y G a U.unop x

/-- Multiplication by any function on the source survives the original direct-image map.
This includes every homogeneous element of the structural Rees algebra. -/
theorem moduleCohomologyPushforwardMap_globalScalar (G : Y.Modules) (a : Γ(Y, ⊤))
    (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X ((Scheme.Modules.pushforward p).obj G)) q) :
    moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map
        ((Scheme.Modules.pushforward p).map
          (Scheme.Modules.globalScalarEndomorphism Y G a))) q x) =
    Sheaf.H.map (moduleScalarOfGlobal Y G a) q
      (moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q x) := by
  simpa only [globalScalarEndomorphism_toSheaf] using
    moduleCohomologyPushforwardMap_naturality p
      (Scheme.Modules.globalScalarEndomorphism Y G a) q x

/-- A sectionwise homogeneous multiplication square gives the identical square on
original cohomology, with the actual target global-function action. -/
theorem moduleSectionsPushforwardCohomology_homogeneous
    {A : Type u} [CommRing A] (α : A →+* Γ(X, ⊤))
    {M M' : X.Modules} (G : Y.Modules) (f : M ⟶ M')
    (e : moduleSectionsPresheaf X α M ⟶
      moduleSectionsPresheaf X α ((Scheme.Modules.pushforward p).obj G))
    (e' : moduleSectionsPresheaf X α M' ⟶
      moduleSectionsPresheaf X α ((Scheme.Modules.pushforward p).obj G))
    (a : Γ(Y, ⊤))
    (h : (moduleSectionsPresheafFunctor X α).map f ≫ e' =
      e ≫ (moduleSectionsPresheafFunctor X α).map
        ((Scheme.Modules.pushforward p).map
          (Scheme.Modules.globalScalarEndomorphism Y G a)))
    (q : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) q) :
    moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q
      (Sheaf.H.map (moduleSectionsAddSheafMap X α e') q
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map f) q x)) =
    Sheaf.H.map (moduleScalarOfGlobal Y G a) q
      (moduleCohomologyMapAlong p (𝟙 ((Scheme.Modules.pushforward p).obj G)) q
        (Sheaf.H.map (moduleSectionsAddSheafMap X α e) q x)) := by
  have hs := moduleSectionsCohomologyMap_square X α e e'
    ((moduleSectionsPresheafFunctor X α).map f)
    ((moduleSectionsPresheafFunctor X α).map
      ((Scheme.Modules.pushforward p).map
        (Scheme.Modules.globalScalarEndomorphism Y G a))) h q x
  change Sheaf.H.map (moduleSectionsAddSheafMap X α e') q
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map f) q x) =
    Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map
      ((Scheme.Modules.pushforward p).map
        (Scheme.Modules.globalScalarEndomorphism Y G a))) q
      (Sheaf.H.map (moduleSectionsAddSheafMap X α e) q x) at hs
  rw [hs, moduleCohomologyPushforwardMap_globalScalar]

end AlgebraicGeometry.Scheme.Cohomology
