/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootPointedSection
public import Aglib.RingTheory.Henselian.StrictHenselization.PrimitiveRootsLocalStages

/-! # The original pointed lift and primitive root at one genuine stage

Refine the actual section stage once to carry the single chosen primitive
root. Original diagram and cone naturality retain the structural map and
the specified point, without changing the colimit, local stage or cover.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

/-- One genuine pointed neighborhood carries the descended original lift and
one primitive root, which retains its order in the native point localization. -/
theorem exists_rootStage_pointedData
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : R))
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of (RootAlgebra N f))) [IsFinite p] [Etale p]
    (X₀ : GeometricEtaleNeighborhood R Ω) :
    letI : IsLocalRing (RootAlgebra N f) := parameterRoot_isLocalRing R f hf N hN
    letI : IsLocalRing (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) f)) :=
      GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
    ∀ y : Z, p y = IsLocalRing.closedPoint (RootAlgebra N f) →
    ∃ a : Spec (.of (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) f))) ⟶ Z,
      a ≫ p = Spec.map (CommRingCat.ofHom
        (rootBaseChangeHom (GeometricEtaleColimit R Ω) N f).toRingHom) ∧
      a (IsLocalRing.closedPoint _) = y ∧
      ∃ (ζ : GeometricEtaleColimit R Ω), IsPrimitiveRoot ζ N ∧
      ∃ (Y : GeometricEtaleNeighborhood R Ω) (_ : X₀ ⟶ Y) (z : Y.algebra)
        (b : (rootDiagram R Ω N f).obj (op Y) ⟶ Z),
        GeometricEtaleColimit.ι R Ω Y z = ζ ∧ IsPrimitiveRoot z N ∧
        IsPrimitiveRoot (algebraMap Y.algebra
          (GeometricEtaleColimit.stageLocalRing R Ω Y) z) N ∧
        b ≫ p = (rootStructure R Ω N f).app (op Y) ∧
        (rootCone R Ω N f).π.app (op Y) ≫ b = a := by
  let : IsLocalRing (RootAlgebra N f) := parameterRoot_isLocalRing R f hf N hN
  let : IsLocalRing (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) f)) :=
    GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
  intro y hy
  obtain ⟨a, ha, hay, X, g, b, hb, hba⟩ :=
    exists_rootStage_lift_through_closedPoint R Ω N hN f hf p X₀ y hy
  obtain ⟨ζ, hζ, Y, k, z, hz, hpz, hpl⟩ :=
    GeometricEtaleColimit.exists_primitiveRoot_pointLocalization_over R Ω N hN hunit X
  refine ⟨a, ha, hay, ζ, hζ, Y, g ≫ k, z,
    (rootDiagram R Ω N f).map k.op ≫ b, hz, hpz, hpl, ?_, ?_⟩
  · rw [Category.assoc, hb]
    exact ((rootStructure R Ω N f).naturality k.op).trans (Category.comp_id _)
  · rw [← Category.assoc, (rootCone R Ω N f).w k.op, hba]

end AlgebraicGeometry.Scheme.Kummer
