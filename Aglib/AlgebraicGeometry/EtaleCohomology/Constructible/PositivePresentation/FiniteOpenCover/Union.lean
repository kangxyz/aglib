/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.FiniteOpenCover
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-! # Original bounded generators on finite unions of opens

The actual overlap, inclusions and union form the same bounded-generator
pushout without requiring the union to be the whole original test scheme.
Finite gluing consequently applies to any finite-colimit-stable property,
using a family of opens closed under intersections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace FiniteOpenCover

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- The original intersection-to-union square on an unchanged etale object. -/
def openUnionSquare (V W : U.left.Opens) : Square X.Etale where
  X₁ := openChart U (V ⊓ W)
  X₂ := openChart U V
  X₃ := openChart U W
  X₄ := openChart U (V ⊔ W)
  f₁₂ := openMap U inf_le_left
  f₁₃ := openMap U inf_le_right
  f₂₄ := openMap U le_sup_left
  f₃₄ := openMap U le_sup_right
  fac := by
    apply MorphismProperty.Over.Hom.ext
    change U.left.homOfLE inf_le_left ≫ U.left.homOfLE le_sup_left =
      U.left.homOfLE inf_le_right ≫ U.left.homOfLE le_sup_right
    apply (cancel_mono (V ⊔ W).ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι]

instance openMap_mono {V W : U.left.Opens} (h : V ≤ W) : Mono (openMap U h) := by
  apply Functor.mono_of_mono_map (Scheme.Etale.forget X ⋙ Over.forget X)
  exact inferInstanceAs (Mono (U.left.homOfLE h))

instance openUnionSquare_left_mono (V W : U.left.Opens) :
    Mono (openUnionSquare U V W).f₂₄ := openMap_mono U le_sup_left

instance openUnionSquare_right_mono (V W : U.left.Opens) :
    Mono (openUnionSquare U V W).f₃₄ := openMap_mono U le_sup_right

/-- The original open-overlap square is cartesian over the actual union. -/
theorem openUnionSquare_isPullback (V W : U.left.Opens) :
    (openUnionSquare U V W).IsPullback := by
  apply CategoryTheory.IsPullback.of_map (Scheme.Etale.forget X ⋙ Over.forget X)
    (openUnionSquare U V W).fac
  exact AlgebraicGeometry.isPullback_opens_inf_le le_sup_left le_sup_right

/-- The original two inclusions cover their actual union. -/
theorem openUnionSquare_cover (V W : U.left.Opens) :
    Sieve.ofTwoArrows (openUnionSquare U V W).f₂₄
      (openUnionSquare U V W).f₃₄ ∈ X.smallEtaleTopology (openChart U (V ⊔ W)) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  rcases x.property with hx | hx
  · refine ⟨WalkingPair.left, ⟨x.val, hx⟩, ?_⟩
    change U.left.homOfLE le_sup_left _ = x
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _
  · refine ⟨WalkingPair.right, ⟨x.val, hx⟩, ?_⟩
    change U.left.homOfLE le_sup_right _ = x
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _

/-- Finite-colimit-stable properties glue on the original binary open union,
using its original overlap rather than a replacement coefficient model. -/
theorem prop_openChart_sup (n : ℕ)
    (P : ObjectProperty (BoundedPresentation.Coefficient X n))
    [P.IsClosedUnderFiniteColimits] (V W : U.left.Opens)
    (hV : P (BoundedPresentation.free X n (openChart U V)))
    (hW : P (BoundedPresentation.free X n (openChart U W)))
    (hVW : P (BoundedPresentation.free X n (openChart U (V ⊓ W)))) :
    P (BoundedPresentation.free X n (openChart U (V ⊔ W))) := by
  have hp := coefficientSquare_isPushout X n (openUnionSquare U V W)
    (openUnionSquare_isPullback U V W) (openUnionSquare_cover U V W)
  exact P.prop_of_isColimit hp.isColimit (by
    intro a
    cases a with
    | none => exact hVW
    | some a => cases a <;> assumption)

/-- Finite unions glue an intersection-stable family of original open
coefficient generators. This retains the actual opens and finite union. -/
theorem prop_openChart_finsetSup (n : ℕ)
    (P : ObjectProperty (BoundedPresentation.Coefficient X n))
    [P.IsClosedUnderFiniteColimits]
    (B : U.left.Opens → Prop)
    (hB : ∀ V W, B V → B W → B (V ⊓ W))
    (hP : ∀ V, B V → P (BoundedPresentation.free X n (openChart U V)))
    (hbot : P (BoundedPresentation.free X n (openChart U ⊥)))
    (s : Finset U.left.Opens) (hs : ∀ V ∈ s, B V) :
    P (BoundedPresentation.free X n (openChart U (s.sup id))) := by
  classical
  let Q := fun V => P (BoundedPresentation.free X n (openChart U V))
  have hsup : ∀ V W, Q V → Q W → Q (V ⊓ W) → Q (V ⊔ W) :=
    prop_openChart_sup U n P
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

end FiniteOpenCover
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
