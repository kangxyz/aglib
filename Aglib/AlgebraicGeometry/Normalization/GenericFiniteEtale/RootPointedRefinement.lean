/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootPointedData

/-! # Retaining the original pointed data under a cofinal refinement

A further genuine neighborhood refinement retains the same colimit lift,
primitive root and specified point. The root order is reflected from the
same colimit, not asserted preserved by an arbitrary localization map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

/-- One genuine pointed neighborhood carries the descended original lift and
one primitive root, which retains its order in the native point localization. -/
theorem exists_rootStage_pointedData_refinement
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : R))
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of (RootAlgebra N f))) [IsFinite p] [Etale p]
    (P : GeometricEtaleNeighborhood R Ω → Prop)
    (hP : ∀ X : GeometricEtaleNeighborhood R Ω, ∃ Y, Nonempty (X ⟶ Y) ∧ P Y)
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
        P Y ∧ GeometricEtaleColimit.ι R Ω Y z = ζ ∧ IsPrimitiveRoot z N ∧
        IsPrimitiveRoot (algebraMap Y.algebra
          (GeometricEtaleColimit.stageLocalRing R Ω Y) z) N ∧
        b ≫ p = (rootStructure R Ω N f).app (op Y) ∧
        (rootCone R Ω N f).π.app (op Y) ≫ b = a := by
  let : IsLocalRing (RootAlgebra N f) := parameterRoot_isLocalRing R f hf N hN
  let : IsLocalRing (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) f)) :=
    GeometricEtaleColimit.rootPoint_source_isLocalRing R Ω N hN f hf
  intro y hy
  obtain ⟨a, ha, hay, ζ, hζ, X, g, z, b, hz, hpz, _, hb, hba⟩ :=
    exists_rootStage_pointedData R Ω N hN hunit f hf p X₀ y hy
  obtain ⟨Y, ⟨k⟩, hY⟩ := hP X
  have hzk : GeometricEtaleColimit.ι R Ω Y (k.val z) = ζ :=
    (AlgHom.congr_fun (GeometricEtaleColimit.ι_naturality k) z).trans hz
  have hpow : (k.val z) ^ N = 1 := by
    rw [← map_pow, hpz.pow_eq_one, map_one]
  have hpk : IsPrimitiveRoot (k.val z) N := by
    constructor
    · exact hpow
    · intro m hm
      apply hζ.dvd_of_pow_eq_one m
      rw [← hzk, ← map_pow, hm, map_one]
  have hpl : IsPrimitiveRoot (algebraMap Y.algebra
      (GeometricEtaleColimit.stageLocalRing R Ω Y) (k.val z)) N := by
    constructor
    · rw [← map_pow, hpow, map_one]
    · intro m hm
      apply hζ.dvd_of_pow_eq_one m
      rw [← hzk, ← GeometricEtaleColimit.stageLocalMap_algebraMap R Ω Y (k.val z),
        ← map_pow, hm, map_one]
  refine ⟨a, ha, hay, ζ, hζ, Y, g ≫ k, k.val z,
    (rootDiagram R Ω N f).map k.op ≫ b, hY, hzk, hpk, hpl, ?_, ?_⟩
  · rw [Category.assoc, hb]
    exact ((rootStructure R Ω N f).naturality k.op).trans (Category.comp_id _)
  · rw [← Category.assoc, (rootCone R Ω N f).w k.op, hba]

end AlgebraicGeometry.Scheme.Kummer
