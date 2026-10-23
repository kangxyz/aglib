/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ArtinSite
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Sites.EtaleBaseChangeCoverage
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Actual finite-etale base change as an Artin-site comparison

Surjectivity reflects covering sieves on the actual finite-etale bases. When
native base change is an equivalence, it is therefore an equivalence of these
sites, not merely of the underlying categories.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u v w

variable {X S : Scheme.{u}}
  [IsLocallyArtinian X] [QuasiSeparatedSpace X]
  [IsLocallyArtinian S] [QuasiSeparatedSpace S]

/-- The actual base-change functor preserves and reflects the induced covers. -/
theorem artinBaseChange_pushforward_mem_iff (f : S ⟶ X) [Surjective f]
    {U : FiniteEtale X} (R : Sieve U) :
    R.functorPushforward (baseChange f) ∈ artinTopology S _ ↔
      R ∈ artinTopology X U := by
  simp only [artinTopology, Functor.mem_inducedTopology_iff_of_isCoverDense]
  rw [← Sieve.functorPushforward_comp]
  change R.functorPushforward (toEtale X ⋙ siteBaseChange f) ∈
    S.smallEtaleTopology _ ↔ R.functorPushforward (toEtale X) ∈ X.smallEtaleTopology _
  rw [Sieve.functorPushforward_comp]
  exact siteBaseChange_pushforward_mem_iff f _

/-- A native finite-etale equivalence over a surjective map is a dense site equivalence. -/
instance artinBaseChange_isDenseSubsite (f : S ⟶ X) [Surjective f]
    [(baseChange f).IsEquivalence] :
    (baseChange f).IsDenseSubsite (artinTopology X) (artinTopology S) where
  functorPushforward_mem_iff := artinBaseChange_pushforward_mem_iff f _

/-- The induced sheaf equivalence retains the actual finite-etale base-change functor. -/
def artinBaseChangeSheafEquivalence (f : S ⟶ X) [Surjective f]
    [(baseChange f).IsEquivalence] (A : Type v) [Category.{w} A] :
    Sheaf (artinTopology X) A ≌ Sheaf (artinTopology S) A := by
  let : (baseChange f).asEquivalence.symm.inverse.IsDenseSubsite
      (artinTopology X) (artinTopology S) := artinBaseChange_isDenseSubsite f
  exact ((baseChange f).asEquivalence.symm.sheafCongr
    (artinTopology S) (artinTopology X) A).symm

end AlgebraicGeometry.Scheme.FiniteEtale
