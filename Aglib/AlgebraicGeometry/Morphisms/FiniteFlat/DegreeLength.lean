/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Artinian.FiniteAlgebra
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeLength` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`d58c78021fa48ff0f5d4d511d1ddfd5278ed9c2d537dd827c2c579d72bc1426b`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing
open AlgebraicGeometry.Scheme.Hom
namespace AlgebraicGeometry.Scheme.Hom.FiniteFlat
section FiniteSchemeDegree

universe u
variable (k : Type u) [Field k] (D : Scheme.{u}) (q : D ⟶ Spec (.of k)) [IsFinite q]

/-- Finiteness of the actual coordinate algebra, with scalars supplied by the
actual structural map used in `Abel.finiteSchemeDegree`. -/
theorem finite_coordinate_algebra :
    letI : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
    Module.Finite k Γ(D, ⊤) := by
  let : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
  apply RingHom.finite_algebraMap.mp
  exact q.finite_appTop.comp
    (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of k)).inv.hom)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).surjective)

/-- The actual finite-scheme degree is a full local-length/residue-degree sum,
including nilpotent structure. Identifying these primary factors with the actual
divisor stalks is a separate geometric comparison for the Cartier-degree target. -/
theorem finiteSchemeDegree_eq_sum_component_lengths :
    letI : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
    letI : Module.Finite k Γ(D, ⊤) := finite_coordinate_algebra k D q
    let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
    letI := Fintype.ofFinite (MaximalSpectrum Γ(D, ⊤))
    ∃ n : ℕ, AlgebraicGeometry.Scheme.Hom.finiteSchemeDegree k q =
      ∑ m : MaximalSpectrum Γ(D, ⊤),
        (Module.length (Algebra.ArtinComponent Γ(D, ⊤) n m)
          (Algebra.ArtinComponent Γ(D, ⊤) n m)).toNat *
          Module.finrank k (Γ(D, ⊤) ⧸ m.asIdeal) := by
  classical
  let : Algebra k Γ(D, ⊤) := coordinateAlgebra k (Over.mk q)
  let : Module.Finite k Γ(D, ⊤) := finite_coordinate_algebra k D q
  let : IsArtinianRing Γ(D, ⊤) := IsArtinianRing.of_finite k Γ(D, ⊤)
  let := Fintype.ofFinite (MaximalSpectrum Γ(D, ⊤))
  exact Algebra.exists_finrank_eq_sum_maximal_quotient_degree Γ(D, ⊤) k

end FiniteSchemeDegree
end AlgebraicGeometry.Scheme.Hom.FiniteFlat
