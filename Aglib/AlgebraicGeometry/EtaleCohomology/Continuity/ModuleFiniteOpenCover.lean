/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FreeRepresentableCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleCoefficientSystem
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FiniteOpenCover.Union

/-! # Original native module generators on finite open covers

Only the coefficient-free original open charts and union squares are reused
from the bounded-coefficient geometry. All coefficient objects and arrows
below are original ModuleCat-valued free sheaves over the arbitrary ring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
namespace FiniteOpenCover

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

open Constructible.PositivePresentation.FiniteOpenCover

variable (R : Type (u + 1)) [Ring R] {X : Scheme.{u}} (U : X.Etale)

/-- The original native free representable, without a replacement generator. -/
abbrev free (X : Scheme.{u}) (V : X.Etale) : Coefficient R X :=
  ModuleCat.Sheaf.freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R V

/-- Finite-colimit-stable properties glue on the original binary open union,
using its original overlap rather than a replacement coefficient model. -/
theorem prop_openChart_sup (P : ObjectProperty (Coefficient R X))
    [P.IsClosedUnderFiniteColimits] (V W : U.left.Opens)
    (hV : P (free R X (openChart U V)))
    (hW : P (free R X (openChart U W)))
    (hVW : P (free R X (openChart U (V ⊓ W)))) :
    P (free R X (openChart U (V ⊔ W))) := by
  have hp := ModuleCat.Sheaf.freeRepresentable_square_isPushout.{u + 1, u, u + 1, 0}
    X.smallEtaleTopology R (openUnionSquare U V W)
    (openUnionSquare_isPullback U V W) (openUnionSquare_cover U V W)
  exact P.prop_of_isColimit hp.isColimit (by
    intro a
    cases a with
    | none => exact hVW
    | some a => cases a <;> assumption)

/-- Finite unions glue an intersection-stable family of original open
coefficient generators. This retains the actual opens and finite union. -/
theorem prop_openChart_finsetSup (P : ObjectProperty (Coefficient R X))
    [P.IsClosedUnderFiniteColimits]
    (B : U.left.Opens → Prop)
    (hB : ∀ V W, B V → B W → B (V ⊓ W))
    (hP : ∀ V, B V → P (free R X (openChart U V)))
    (hbot : P (free R X (openChart U ⊥)))
    (s : Finset U.left.Opens) (hs : ∀ V ∈ s, B V) :
    P (free R X (openChart U (s.sup id))) := by
  classical
  let Q := fun V => P (free R X (openChart U V))
  have hsup : ∀ V W, Q V → Q W → Q (V ⊓ W) → Q (V ⊔ W) :=
    prop_openChart_sup R U P
  have main (s : Finset U.left.Opens) :
      (∀ V ∈ s, B V) → Q (s.sup id) ∧ ∀ W, B W → Q (s.sup id ⊓ W) := by
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa only [Finset.sup_empty, bot_inf_eq] using
        (show Q ⊥ ∧ ∀ W, B W → Q ⊥ from ⟨hbot, fun _ _ => hbot⟩)
    | @insert V s hVs ih =>
      intro hs
      have hV := hs V (Finset.mem_insert_self V s)
      obtain ⟨hS, hSW⟩ := ih (fun W hW => hs W (Finset.mem_insert_of_mem hW))
      rw [Finset.sup_insert]
      constructor
      · exact hsup V (s.sup id) (hP V hV) hS
          (by simpa only [inf_comm] using hSW V hV)
      · intro W hW
        rw [inf_sup_right]
        apply hsup (V ⊓ W) (s.sup id ⊓ W) (hP _ (hB V W hV hW)) (hSW W hW)
        simpa only [inf_assoc, inf_comm, inf_left_comm, inf_idem,
          inf_left_idem, inf_right_idem] using
          hSW (V ⊓ W) (hB V W hV hW)
  exact (main s hs).1


/-- A finite original open cover assembles the unchanged native generator
from any intersection-stable family of charts with the chosen property. -/
theorem prop_free_of_finiteCover
    (P : ObjectProperty (Coefficient R X)) [P.IsClosedUnderFiniteColimits]
    (B : U.left.Opens → Prop)
    (hB : ∀ V W, B V → B W → B (V ⊓ W))
    (hP : ∀ V, B V → P (free R X (openChart U V)))
    (hbot : P (free R X (openChart U ⊥)))
    (s : Finset U.left.Opens) (hs : ∀ V ∈ s, B V) (hcover : s.sup id = ⊤) :
    P (free R X U) := by
  have h := prop_openChart_finsetSup R U P B hB hP hbot s hs
  rw [hcover] at h
  let e : openChart U ⊤ ≅ U := MorphismProperty.Over.isoMk U.left.topIso rfl
  exact P.prop_of_iso
    ((ModuleCat.Sheaf.freeRepresentableFunctor.{u + 1, u + 1, u, 0}
      X.smallEtaleTopology R).mapIso e) h

end FiniteOpenCover
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
