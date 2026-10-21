/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.PointedRunTransport

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ResolutionGeometry`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`43f3f279e599a901f2de5b7bb01324a0843bf8a6d557dbd09923192f55bef54a`.
Only source136–185 unchanged-open comparisons and lifted actual sections. The recursive unchanged
  theorem is supplied by the existing stronger relative_unchanged theorem, specialized to the same
  State.map and fixed original point. All four general blowup-family inputs remain explicit.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

section PointedRunUnchangedOpen


/-! Every actual point blowup in the finite trace preserves the inverse
image of any original open disjoint from the fixed original point. Hence
sections and arbitrary base changes landing in that same open lift through
the canonical isomorphism, with their actual structural triangles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}

namespace Run
variable {hex : NoetherianBlowupExistence.{u}} {hp : NoetherianBlowupProper.{u}}
  {hatlas : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}

lemma unchanged {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
    (T : Run hex hp hatlas hbc S) (U : X.Opens)
    (hU : Disjoint (U : Set X) (Set.range q₀)) (hS : IsIso (S.map ∣_ U)) :
    IsIso (T.toOriginal ∣_ U) :=
  relative_unchanged T S.map q₀ S.point_triangle U hU hS

variable {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
  (T : Run hex hp hatlas hbc S) (U : X.Opens)
  (hU : Disjoint (U : Set X) (Set.range q₀)) [IsIso (S.map ∣_ U)]

/-- Identify the inverse image of an original open disjoint from `q₀` with that open, assuming the
starting map is an isomorphism there. -/
def unchangedIso : (T.toOriginal ⁻¹ᵁ U).toScheme ≅ U.toScheme := by
  let := unchanged T U hU inferInstance
  exact asIso (T.toOriginal ∣_ U)

@[reassoc] lemma unchangedIso_triangle :
    (unchangedIso T U hU).hom ≫ U.ι = (T.toOriginal ⁻¹ᵁ U).ι ≫ T.toOriginal :=
  morphismRestrict_ι _ _

include hU in
lemma pullback_isIso {A : Scheme.{u}} (j : A ⟶ X) (hj : Set.range j ⊆ U) :
    IsIso (pullback.snd T.toOriginal j) := by
  let := unchanged T U hU inferInstance
  exact AlgebraicGeometry.Scheme.Hom.isIso_pullback_of_range_subset T.toOriginal U j hj

/-- Lift the same actual section of any fixed unchanged open. -/
def liftedSection {A : Scheme.{u}} (s : A ⟶ U.toScheme) : A ⟶ T.source :=
  s ≫ (unchangedIso T U hU).inv ≫ (T.toOriginal ⁻¹ᵁ U).ι

@[reassoc] lemma liftedSection_triangle {A : Scheme.{u}} (s : A ⟶ U.toScheme) :
    liftedSection T U hU s ≫ T.toOriginal = s ≫ U.ι := by
  simp only [liftedSection, Category.assoc]
  rw [← unchangedIso_triangle T U hU, Iso.inv_hom_id_assoc]

end Run
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end PointedRunUnchangedOpen
