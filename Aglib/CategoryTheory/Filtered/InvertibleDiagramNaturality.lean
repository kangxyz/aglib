/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Filtered.InvertibleDiagram

/-!
# Naturality of canonical comparisons in invertible cofiltered diagrams

Canonical comparisons commute with morphisms of diagrams over any index
functor. No cofinality assumption on that index functor is necessary: the
image of any common predecessor computes the target comparison. They also
commute with postcomposition by an arbitrary functor.
-/

@[expose] public noncomputable section

universe vJ vK vE vE' uJ uK uE uE'

namespace CategoryTheory.Functor

open Opposite IsIso

variable {J : Type uJ} [Category.{vJ} J] [IsCofilteredOrEmpty J]
  {K : Type uK} [Category.{vK} K] [IsCofilteredOrEmpty K]
  {E : Type uE} [Category.{vE} E]
  {F : Jᵒᵖ ⥤ E} {G : Kᵒᵖ ⥤ E}
  [∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsIso (F.map f)]
  [∀ (i j : Kᵒᵖ) (f : i ⟶ j), IsIso (G.map f)]

/-- Any morphism of invertible diagrams over an index functor commutes with
canonical comparison maps. The index functor need not be cofinal. -/
@[reassoc]
theorem cofilteredComparison_natTrans (B : J ⥤ K) (α : F ⟶ B.op ⋙ G) (j k : J) :
    α.app (op j) ≫ (G.cofilteredComparison (B.obj j) (B.obj k)).hom =
      (F.cofilteredComparison j k).hom ≫ α.app (op k) := by
  let i := IsCofiltered.min j k
  let a : i ⟶ j := IsCofiltered.minToLeft j k
  let b : i ⟶ k := IsCofiltered.minToRight j k
  have ha : F.map a.op ≫ α.app (op i) =
      α.app (op j) ≫ G.map (B.map a).op := α.naturality a.op
  have hb : F.map b.op ≫ α.app (op i) =
      α.app (op k) ≫ G.map (B.map b).op := α.naturality b.op
  rw [G.cofilteredComparison_eq_span (B.map a) (B.map b),
    F.cofilteredComparison_eq_span a b]
  simp only [cofilteredSpanIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  apply (cancel_mono (G.map (B.map b).op)).mp
  simp only [Category.assoc, inv_hom_id, Category.comp_id]
  rw [← hb]
  simpa only [inv_hom_id_assoc] using ha.symm

/-- Natural isomorphisms over any index functor intertwine the canonical
comparison isomorphisms. -/
theorem cofilteredComparison_natIso (B : J ⥤ K) (α : F ≅ B.op ⋙ G) (j k : J) :
    α.app (op j) ≪≫ G.cofilteredComparison (B.obj j) (B.obj k) =
      F.cofilteredComparison j k ≪≫ α.app (op k) := by
  apply Iso.ext
  exact cofilteredComparison_natTrans B α.hom j k

omit [IsCofilteredOrEmpty J] [IsCofilteredOrEmpty K] in
local instance reindexedMapIsIso (B : J ⥤ K) :
    ∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsIso ((B.op ⋙ G).map f) :=
  fun _ _ f => inferInstanceAs (IsIso (G.map (B.op.map f)))

/-- Reindexing an invertible diagram preserves its canonical comparisons,
without a cofinality hypothesis on the index functor. -/
theorem cofilteredComparison_precomp (B : J ⥤ K) (j k : J) :
    (B.op ⋙ G).cofilteredComparison j k =
      G.cofilteredComparison (B.obj j) (B.obj k) := by
  let a := IsCofiltered.minToLeft j k
  let b := IsCofiltered.minToRight j k
  rw [(B.op ⋙ G).cofilteredComparison_eq_span a b,
    G.cofilteredComparison_eq_span (B.map a) (B.map b)]
  rfl

omit [IsCofilteredOrEmpty J] in
local instance postcomposedMapIsIso {E' : Type uE'} [Category.{vE'} E'] (H : E ⥤ E') :
    ∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsIso ((F ⋙ H).map f) :=
  fun _ _ f => inferInstanceAs (IsIso (H.map (F.map f)))

/-- Postcomposition by any functor preserves canonical comparison isomorphisms. -/
theorem cofilteredComparison_postcomp {E' : Type uE'} [Category.{vE'} E']
    (H : E ⥤ E') (j k : J) :
    H.mapIso (F.cofilteredComparison j k) = (F ⋙ H).cofilteredComparison j k := by
  let a := IsCofiltered.minToLeft j k
  let b := IsCofiltered.minToRight j k
  rw [F.cofilteredComparison_eq_span a b, (F ⋙ H).cofilteredComparison_eq_span a b]
  apply Iso.ext
  simp [cofilteredSpanIso]

end CategoryTheory.Functor
