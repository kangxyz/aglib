/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DisjointSections
public import Mathlib.AlgebraicGeometry.LimitsOver

/-! # Original sections on coproducts of geometric neighborhood representatives -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Etale)

/-- The actual coproduct structure map is étale; no quasi-compactness or finite
presentation hypothesis on the chosen representatives is imposed. -/
instance coproductStructure_etale : Etale (Sigma.desc (fun i => (U i).hom)) := by
  let : IsZariskiLocalAtSource (fun {V W : Scheme.{u}} (f : V ⟶ W) => Etale f) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource (@Etale.{u}) (@RingHom.Etale.{u})
      Etale.instHasRingHomPropertyEtale
  exact IsZariskiLocalAtSource.sigmaDesc
    (P := fun {V W : Scheme.{u}} (f : V ⟶ W) => Etale f) (fun i => (U i).prop)

/-- The actual scheme coproduct as an object of the original small étale site. -/
abbrev coproductEtale : X.Etale := Scheme.Etale.mk (Sigma.desc (fun i => (U i).hom))

/-- The literal coproduct inclusion in the original small étale category. -/
abbrev coproductEtaleInclusion (i : ι) : U i ⟶ coproductEtale U :=
  MorphismProperty.Over.homMk (Sigma.ι (fun i => (U i).left) i) (Sigma.ι_comp_desc _ _)

instance (i : ι) : Mono (coproductEtaleInclusion U i) where
  right_cancellation {Z} a b h := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (Sigma.ι (fun i => (U i).left) i)).mp
    exact congrArg (fun k : Z ⟶ coproductEtale U => k.left) h

/-- The actual summand inclusions cover the coproduct object. -/
theorem coproductEtaleInclusion_cover :
    Sieve.ofArrows U (coproductEtaleInclusion U) ∈ X.smallEtaleTopology (coproductEtale U) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (coproductEtaleInclusion U)).mpr
  change (⋃ i, Set.range (Sigma.ι (fun i => (U i).left) i)) = Set.univ
  exact (sigmaOpenCover (fun i => (U i).left)).iUnion_range

/-- The literal section restriction fan on these representatives is a product. -/
def coproductSectionsFanIsLimit (F : AbelianSheaf.{u, u + 1} X) :
    IsLimit (disjointSectionsFan F (coproductEtaleInclusion U)) := by
  apply disjointSectionsFanIsLimit F (coproductEtaleInclusion U)
    (coproductEtaleInclusion_cover U)
  intro i j hij Z a b h
  exact isEmpty_of_commSq_sigmaι_of_ne
    (g := fun i => (U i).left) (a := a.left) (b := b.left)
    ⟨congrArg (fun k : Z ⟶ coproductEtale U => k.left) h⟩ hij

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
