/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.SectionExactness
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ResolutionSections
public import Aglib.CategoryTheory.Abelian.Injective.MappedResolution
public import Mathlib.CategoryTheory.Sites.Continuous

/-! # Actual restricted resolutions from represented acyclicity on a basis

The original restriction of an injective resolution is exact when the original
represented Ext vanishes on a covering object basis. The basis covers may be
arbitrary small families. With the structural right-adjoint hypotheses, this
is the actual target injective resolution used in the canonical Ext comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe c h c' h' t e k

namespace CategoryTheory.Sheaf.BasisAcyclicity

variable {C : Type c} [Category.{h} C] {D : Type c'} [Category.{h'} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max h h' t}]
  [HasSheafify K AddCommGrpCat.{max h h' t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max h h' t})]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).Additive]
  [HasExt.{e} (Sheaf K AddCommGrpCat.{max h h' t})]
  (B : C → Prop)
  (hB : ∀ W : C, ∃ (ι : Type k) (U : ι → Over W),
    Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W ∧
      ∀ i, B (U i).left)
  {F : Sheaf K AddCommGrpCat.{max h h' t}} (I : InjectiveResolution F)
  (hF : ∀ W, B W → ∀ n : ℕ,
    ∀ x : Ext (Hypercohomology.freeAbelianSheaf.{max h t} K (G.obj W)) F (n + 1), x = 0)

include hB hF in
/-- Original represented acyclicity on a covering basis makes the literal
restricted injective complex exact in every positive degree. -/
theorem restriction_resolution_exactAt_succ (n : ℕ) :
    (((G.sheafPushforwardContinuous AddCommGrpCat J K).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).ExactAt (n + 1) := by
  apply exactAt_of_sections_on_basis B hB
  intro W hW
  exact resolution_sections_exactAt_succ K I (G.obj W) n (hF W hW n)

variable [PreservesFiniteLimits (G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K)]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).PreservesInjectiveObjects]

/-- The actual restriction of the original resolution, not a chosen replacement,
is an injective resolution of the restricted coefficient. -/
def restrictedInjectiveResolution :
    InjectiveResolution ((G.sheafPushforwardContinuous AddCommGrpCat J K).obj F) :=
  I.mapOfExactAt (G.sheafPushforwardContinuous AddCommGrpCat J K)
    (restriction_resolution_exactAt_succ G J K B hB I hF)

end CategoryTheory.Sheaf.BasisAcyclicity
