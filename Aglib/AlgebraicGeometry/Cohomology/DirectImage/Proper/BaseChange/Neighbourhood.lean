/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.BaseChange.Affine

/-!
# Actual target neighbourhoods for original proper scalar base change

The basic-open proper criterion gives a genuine open of the original locally
Noetherian target. Every affine scheme mapping into this open has an actual
ring map into its original affine coordinate, and the unchanged cohomology
comparison for that ring map is invertible. No cover, map family or matching
condition is assumed, and the new affine scheme may be non-Noetherian.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Surjectivity on a prime residue field supplies a genuine open neighbourhood
of the corresponding target point. Every affine scheme mapping into that open
has an original scalar comparison which is invertible and whose scheme map
is exactly its given map into the original target. No reducedness is required. -/
theorem exists_open_moduleCohomologyBaseChangeMap_isIso_of_epi_residue_on_affine
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
    (p : PrimeSpectrum R)
    (hres : Epi (moduleCohomologyBaseChangeMap (pullback.snd f j)
      (algebraMap R p.asIdeal.ResidueField)
      ((Scheme.Modules.pullback (pullback.fst f j)).obj M) q)) :
    ∃ U : Y.Opens, j p ∈ U ∧
      ∀ (B : CommRingCat.{u}) (t : Spec B ⟶ U.toScheme),
        ∃ σ : R →+* B, Spec.map (CommRingCat.ofHom σ) ≫ j = t ≫ U.ι ∧
          IsIso (moduleCohomologyBaseChangeMap (pullback.snd f j) σ
            ((Scheme.Modules.pullback (pullback.fst f j)).obj M) q) := by
  obtain ⟨r, hr, hbase⟩ :=
    exists_basicOpen_moduleCohomologyBaseChangeMap_isIso_on_affine_of_epi_residue_of_proper
      f M hM hflat q j p hres
  let k : Spec (CommRingCat.of (Localization.Away r)) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ j
  let U := k.opensRange
  have hp : j p ∈ U := by
    rw [show U = k.opensRange from rfl, Scheme.Hom.opensRange_comp,
      Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) r]
    exact ⟨p, hr, rfl⟩
  let l : U.toScheme ⟶ Spec (CommRingCat.of (Localization.Away r)) :=
    IsOpenImmersion.lift k U.ι (by
      rw [Scheme.Opens.range_ι]
      exact Set.Subset.rfl)
  refine ⟨U, hp, ?_⟩
  intro B t
  let τ := Spec.preimage (t ≫ l)
  refine ⟨τ.hom.comp (algebraMap R (Localization.Away r)), ?_, hbase B τ.hom⟩
  change Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)) ≫ τ) ≫ j =
    t ≫ U.ι
  rw [Spec.map_comp]
  change (Spec.map (Spec.preimage (t ≫ l)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ≫ j = t ≫ U.ι
  rw [Spec.map_preimage, Category.assoc, Category.assoc]
  change t ≫ l ≫ k = t ≫ U.ι
  rw [IsOpenImmersion.lift_fac]

end AlgebraicGeometry.Scheme.Cohomology
