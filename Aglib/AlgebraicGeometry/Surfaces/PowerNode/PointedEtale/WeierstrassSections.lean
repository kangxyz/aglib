/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.Weierstrass
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.Unchanged

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ResolutionGeometry`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`43f3f279e599a901f2de5b7bb01324a0843bf8a6d557dbd09923192f55bef54a`.
Only source286–303: the same actual infinity section lifted through the original residue-node
  complement, with its modification and structural triangles. The original run, schemes, residue
  field and all four blowup-family inputs remain fixed.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Blowup
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π)
  (n : ℕ) (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : Scheme.Blowup.NoetherianBlowupExistence.{u})
  (hp : Scheme.Blowup.NoetherianBlowupProper.{u})
  (hatlas : Scheme.Blowup.BlowupAffineAtlas.{u}) (hbc : Scheme.Blowup.BlowupFlatBaseChange.{u})

/-- The original infinity section is lifted through its same actual complement. -/
def infinityLift : Spec (.of R) ⟶ (originalRun M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).source
  := by
  let : IsIso ((initialState M π hπ n hn a ha he ρ hρ).map ∣_ residueNodeComplement W x y he) := by
    change IsIso ((𝟙 (scheme W)) ∣_ _); infer_instance
  exact Run.liftedSection (originalRun M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
    (residueNodeComplement W x y he) (originalComplement_disjoint he) (infinityComplementSection W
      x y he)

@[reassoc] lemma infinityLift_triangle :
    infinityLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
      modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc = infinitySection W := by
  let : IsIso ((initialState M π hπ n hn a ha he ρ hρ).map ∣_ residueNodeComplement W x y he) := by
    change IsIso ((𝟙 (scheme W)) ∣_ _); infer_instance
  rw [infinityLift, modification, Run.liftedSection_triangle, infinityComplementSection_ι]

@[reassoc] lemma infinityLift_structure :
    infinityLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
      modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W = 𝟙 _ := by
  rw [← Category.assoc, infinityLift_triangle, infinitySection_structure]


end AlgebraicGeometry.Scheme.PowerNode.PointedEtale
end
