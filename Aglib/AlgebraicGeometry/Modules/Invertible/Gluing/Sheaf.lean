/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Sections
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing the module sheaf of a rank-one cocycle

The matching-section modules form an actual sheaf of modules on the scheme. The sheaf condition
is proved by gluing the chart components in the original structure sheaf. The local
trivializations are the previously constructed component projections, with their original
transition multiplication equations.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (c : UnitCocycle U)

/-- The presheaf of matching local functions, with its canonical structure-sheaf scalar action. -/
def matchingPresheaf : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj V := ModuleCat.of _ (c.Sections V.unop)
  map {V W} f := ModuleCat.ofHom
    (X := ModuleCat.of (X.ringCatSheaf.obj.obj V) (c.Sections V.unop))
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
      (ModuleCat.of (X.ringCatSheaf.obj.obj W) (c.Sections W.unop)))
    { toFun := c.restrictSections (leOfHom f.unop)
      map_add' := map_add (c.restrictSections (leOfHom f.unop))
      map_smul' := (c.restrictSections (leOfHom f.unop)).map_smulₛₗ }
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact c.restrictSections_refl V.unop
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (c.restrictSections_comp (leOfHom g.unop) (leOfHom f.unop) s).symm

private theorem compatible_components {κ : Type u} (V : κ → X.Opens)
    (s : ∀ a, c.Sections (V a))
    (hs : ∀ a b, c.restrictSections inf_le_left (s a) =
      c.restrictSections inf_le_right (s b))
    (a b : κ) (W : X.Opens) (ha : W ≤ V a) (hb : W ≤ V b) (i : ι) (hi : W ≤ U i) :
    sectionRestrict X (le_inf ha hi) ((s a).val i) =
      sectionRestrict X (le_inf hb hi) ((s b).val i) := by
  have h := congrArg (fun t : c.Sections (V a ⊓ V b) =>
    sectionRestrict X (le_inf (le_inf ha hb) hi) (t.val i)) (hs a b)
  simpa only [restrictSections_apply, sectionRestrict_comp] using h

/-- Matching local functions satisfy the sheaf condition in the native additive presheaf. -/
theorem matchingPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) c.matchingPresheaf.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro κ V sf hsf
  change ∀ a b, c.restrictSections inf_le_left (sf a) =
    c.restrictSections inf_le_right (sf b) at hsf
  have hcomp (i : ι) : TopCat.Presheaf.IsCompatible X.presheaf
      (fun a => V a ⊓ U i) (fun a => (sf a).val i) := by
    intro a b
    exact c.compatible_components V sf hsf a b _
      (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) i
      (inf_le_left.trans inf_le_right)
  have hcover (i : ι) : (⨆ a, V a) ⊓ U i ≤ ⨆ a, V a ⊓ U i :=
    (iSup_inf_eq V (U i)).le
  have hex (i : ι) : ∃ s : Γ(X, (⨆ a, V a) ⊓ U i),
      ∀ a, sectionRestrict X (inf_le_inf (le_iSup V a) le_rfl) s = (sf a).val i :=
    (X.sheaf.existsUnique_gluing' (fun a => V a ⊓ U i) ((⨆ a, V a) ⊓ U i)
      (fun a => homOfLE (inf_le_inf (le_iSup V a) le_rfl)) (hcover i)
      (fun a => (sf a).val i) (hcomp i)).exists
  choose g hg using hex
  have hgr (a : κ) (i : ι) (W : X.Opens) (ha : W ≤ V a) (hi : W ≤ U i) :
      sectionRestrict X (le_inf (ha.trans (le_iSup V a)) hi) (g i) =
        sectionRestrict X (le_inf ha hi) ((sf a).val i) := by
    have h := congrArg (sectionRestrict X (le_inf ha hi)) (hg i a)
    simpa only [sectionRestrict_comp] using h
  have hmatching : g ∈ c.matchingSubmodule (iSup V) := by
    intro W hWV i j hi hj
    have hWcover : W ≤ ⨆ a, W ⊓ V a := by
      rw [← inf_iSup_eq, inf_eq_left.mpr hWV]
    apply X.sheaf.eq_of_locally_eq' (fun a => W ⊓ V a) W
      (fun _ => homOfLE inf_le_left) hWcover
    intro a
    change sectionRestrict X inf_le_left (sectionRestrict X _ (g i)) =
      sectionRestrict X inf_le_left
        ((c.transitionOn i j hi hj : Γ(X, W)) * sectionRestrict X _ (g j))
    rw [map_mul, sectionRestrict_comp, sectionRestrict_transitionOn, sectionRestrict_comp,
      hgr a i _ inf_le_right (inf_le_left.trans hi),
      hgr a j _ inf_le_right (inf_le_left.trans hj)]
    exact (sf a).property (W ⊓ V a) inf_le_right i j
      (inf_le_left.trans hi) (inf_le_left.trans hj)
  refine ⟨⟨g, hmatching⟩, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    funext i
    exact hg i a
  · intro s hs
    apply Subtype.ext
    funext i
    apply X.sheaf.eq_of_locally_eq' (fun a => V a ⊓ U i) ((⨆ a, V a) ⊓ U i)
      (fun a => homOfLE (inf_le_inf (le_iSup V a) le_rfl)) (hcover i)
    intro a
    exact (congrArg (fun t : c.Sections (V a) => t.val i) (hs a)).trans (hg i a).symm

/-- The actual scheme module sheaf obtained by gluing the given rank-one cocycle. -/
def sheaf : X.Modules := ⟨c.matchingPresheaf, c.matchingPresheaf_isSheaf⟩

/-- The original chart-component projection trivializes the actual glued module sheaf. -/
def localIso (j : ι) : (c.sheaf).over (U j) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U j)) :=
  (SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over (U j))).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun V => (c.localSectionsEquiv j (leOfHom V.unop.hom)).toModuleIso) (by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact c.localSectionsEquiv_restrict j (leOfHom f.unop.left) (leOfHom V.unop.hom) s)

/-- The actual local trivializations multiply by the specified transition unit on overlaps. -/
theorem localIso_transition (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
    (s : c.Sections V) :
    (show Γ(X, V) from (c.localIso i).hom.val.app (op (Over.mk (homOfLE hi))) s) =
      (c.transitionOn i j hi hj : Γ(X, V)) *
        (show Γ(X, V) from (c.localIso j).hom.val.app (op (Over.mk (homOfLE hj))) s) :=
  c.localSectionsEquiv_transition i j hi hj s

end AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle
