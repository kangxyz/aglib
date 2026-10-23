/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Hypercohomology.ContinuousPullback
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.RestrictionResolution
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AdjunctionAcyclic

/-! # Canonical original cohomology comparison from basis acyclicity

The map uses the native exact inverse image, its actual counit, and the
normalized constant-integer source isomorphism. Its bijectivity follows from
original represented Ext vanishing on a covering object basis. It commutes
with every additive coefficient morphism. Restriction is only left exact.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe c h c' h' t e e' k

namespace CategoryTheory.Sheaf.BasisAcyclicity

variable {C : Type c} [Category.{h} C] {D : Type c'} [Category.{h'} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max h h' t}]
  [HasSheafify K AddCommGrpCat.{max h h' t}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).Additive]
  [(G.sheafPullback AddCommGrpCat.{max h h' t} J K).Additive]
  [PreservesFiniteLimits (G.sheafPullback AddCommGrpCat.{max h h' t} J K)]
  [PreservesFiniteColimits (G.sheafPullback AddCommGrpCat.{max h h' t} J K)]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max h h' t})]
  [HasExt.{e'} (Sheaf K AddCommGrpCat.{max h h' t})]
  (T : C) (hT : IsTerminal T) (hGT : IsTerminal (G.obj T))

/-- The canonical map on original sheaf cohomology, with the native integer source. -/
def continuousCohomologyMap (F : Sheaf K AddCommGrpCat.{max h h' t}) (n : ℕ) :
    Sheaf.H.{e} ((G.sheafPushforwardContinuous AddCommGrpCat J K).obj F) n →+
      Sheaf.H.{e'} F n := by
  let A := (constantSheaf J AddCommGrpCat.{max h h' t}).obj
    (AddCommGrpCat.of (ULift.{max h h' t} ℤ))
  let q := Hypercohomology.pullbackConstantIntegerIso.{c, h, c', h', t} G J K T hT hGT
  let f : Ext.{e} A ((G.sheafPushforwardContinuous AddCommGrpCat J K).obj F) n →+
      Ext.{e'} ((G.sheafPullback AddCommGrpCat J K).obj A) F n :=
    (G.sheafAdjunctionContinuous AddCommGrpCat J K).extCounitMap A F n
  let s := (((extFunctor.{e'} n).mapIso q.symm.op).app F).addCommGroupIsoToAddEquiv
  exact s.toAddMonoidHom.comp f

omit [(G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).Additive] in
/-- The canonical original cohomology map commutes with arbitrary additive
coefficient morphisms, not only morphisms in a linear subcategory. -/
theorem continuousCohomologyMap_naturality
    {F F' : Sheaf K AddCommGrpCat.{max h h' t}} (f : F ⟶ F') (n : ℕ)
    (x : Sheaf.H.{e} ((G.sheafPushforwardContinuous AddCommGrpCat J K).obj F) n) :
    continuousCohomologyMap G J K T hT hGT F' n
      (Sheaf.H.map ((G.sheafPushforwardContinuous AddCommGrpCat J K).map f) n x) =
    Sheaf.H.map f n (continuousCohomologyMap G J K T hT hGT F n x) := by
  change (Ext.mk₀ (Hypercohomology.pullbackConstantIntegerIso.{c, h, c', h', t}
      G J K T hT hGT).inv).comp
      ((G.sheafAdjunctionContinuous AddCommGrpCat J K).extCounitMap _ F' n
        (x.comp (Ext.mk₀ ((G.sheafPushforwardContinuous AddCommGrpCat J K).map f))
          (Nat.add_zero n))) (Nat.zero_add n) = _
  rw [Adjunction.extCounitMap_naturality]
  exact (Ext.comp_assoc _ _ _ (Nat.zero_add n) (Nat.add_zero n) (by omega)).symm

variable [J.HasSheafCompose (forget AddCommGrpCat.{max h h' t})]
  [PreservesFiniteLimits (G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K)]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h h' t} J K).PreservesInjectiveObjects]
  (B : C → Prop)
  (hB : ∀ W : C, ∃ (ι : Type k) (U : ι → Over W),
    Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W ∧
      ∀ i, B (U i).left)
  {F : Sheaf K AddCommGrpCat.{max h h' t}} (I : InjectiveResolution F)
  (hF : ∀ W, B W → ∀ n : ℕ,
    ∀ x : Ext (Hypercohomology.freeAbelianSheaf.{max h t} K (G.obj W)) F (n + 1), x = 0)

include hB I hF in
/-- Basiswise original acyclicity makes the canonical original map bijective
in every degree, with independent source and target Ext sizes. -/
theorem continuousCohomologyMap_bijective (n : ℕ) :
    Function.Bijective (continuousCohomologyMap G J K T hT hGT F n) := by
  let q := Hypercohomology.pullbackConstantIntegerIso.{c, h, c', h', t} G J K T hT hGT
  let E := (((extFunctor n).mapIso q.symm.op).app F).addCommGroupIsoToAddEquiv
  exact E.bijective.comp
    ((G.sheafAdjunctionContinuous AddCommGrpCat J K).extCounitMap_bijective_of_exactAt I
      (restriction_resolution_exactAt_succ G J K B hB I hF) n)

end CategoryTheory.Sheaf.BasisAcyclicity
