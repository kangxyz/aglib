/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.ZariskiEtale
public import Mathlib.Topology.Sheaves.MayerVietoris

/-! # Two-open Mayer–Vietoris squares in the original small etale site

The four vertices are the original open subschemes and all four arrows are
images of the original inclusions. The proof uses pullbacks and the actual
jointly surjective covering family, without changing the universe of sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (U V : X.Opens)

/-- The original two-open square mapped into the small etale site. -/
abbrev etaleOpenSquare : Square X.Etale :=
  (Opens.mayerVietorisSquare U V).toSquare.map (opensToEtale X)

instance etaleOpenSquare_f₂₄_mono : Mono (etaleOpenSquare U V).f₂₄ :=
  inferInstanceAs (Mono ((opensToEtale X).map (homOfLE le_sup_left : U ⟶ U ⊔ V)))

instance etaleOpenSquare_f₃₄_mono : Mono (etaleOpenSquare U V).f₃₄ :=
  inferInstanceAs (Mono ((opensToEtale X).map (homOfLE le_sup_right : V ⟶ U ⊔ V)))

/-- Intersections compute the pullback of the two original inclusions. -/
theorem etaleOpenSquare_isPullback : (etaleOpenSquare U V).IsPullback := by
  apply Square.IsPullback.map
  apply Square.IsPullback.mk
  refine PullbackCone.IsLimit.mk _ (fun s => homOfLE (le_inf s.fst.le s.snd.le)) ?_ ?_ ?_
  all_goals intros; apply Subsingleton.elim

/-- The original two inclusion maps jointly cover their union in the small etale topology. -/
theorem etaleOpenSquare_cover :
    Sieve.ofTwoArrows (etaleOpenSquare U V).f₂₄ (etaleOpenSquare U V).f₃₄ ∈
      X.smallEtaleTopology (etaleOpenSquare U V).X₄ := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  rcases x.property with hx | hx
  · refine ⟨WalkingPair.left, ⟨x.val, hx⟩, ?_⟩
    change ((opensToEtale X).map (homOfLE le_sup_left : U ⟶ U ⊔ V)).left _ = x
    rw [opensToEtale_map_left]
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _
  · refine ⟨WalkingPair.right, ⟨x.val, hx⟩, ?_⟩
    change ((opensToEtale X).map (homOfLE le_sup_right : V ⟶ U ⊔ V)).left _ = x
    rw [opensToEtale_map_left]
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _

/-- The two-open square with its native small-etale Mayer–Vietoris structure. -/
def etaleOpenMayerVietoris [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    X.smallEtaleTopology.MayerVietorisSquare :=
  GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback (etaleOpenSquare U V)
    (etaleOpenSquare_isPullback U V) (etaleOpenSquare_cover U V)

@[simp]
theorem etaleOpenMayerVietoris_toSquare [HasWeakSheafify X.smallEtaleTopology (Type u)] :
    (etaleOpenMayerVietoris U V).toSquare = etaleOpenSquare U V := rfl

end AlgebraicGeometry.Scheme
