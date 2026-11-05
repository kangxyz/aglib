/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.WholeSectionResidueMarks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FinitePointedStageLift

/-! # Finite pointed stage lifting with the actual canonical model

An original finite source supplies its own Henselian finite-algebra model:
the global sections of the actual neighborhood limit, with its native
limitSourceIso. The actual residue marks feed stage lifting directly.
No finite model, presentation isomorphism or residue fields are assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open GeometricNeighborhood

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Actual finite sources have a common genuine pointed target stage, using
exactly their canonical model and the supplied original component marks. -/
theorem exists_finite_pointed_stage_lift_of_canonical_model
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
    (U : MaximalSpectrum (limitSourceRing R Ω f) → X.Etale)
    (m : ∀ i : MaximalSpectrum (limitSourceRing R Ω f),
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (U i).left)
    (hm : ∀ i : MaximalSpectrum (limitSourceRing R Ω f),
      m i ≫ (U i).hom = limitResidueMap R Ω f i) :
    ∃ (V : GeometricEtaleNeighborhood R Ω)
      (v : (baseChangedDiagram R Ω f).obj (op V) ⟶ Over.mk (coproductEtale U).hom),
      (∀ i : MaximalSpectrum (limitSourceRing R Ω f),
        (localComponentResidueMap (limitSourceRing R Ω f) i ≫
          localComponentInclusion (limitSourceRing R Ω f) i ≫
          (limitSourceIso R Ω f).hom ≫ ((baseChangedCone R Ω f).π.app (op V)).left) ≫
            v.left = m i ≫ Sigma.ι (fun i => (U i).left) i) ∧
      (∀ (M : AbelianSheaf.{u, u + 1} X) (q : ℕ) (δ : Sheaf.H.{u + 2} M q),
        cohomologyPullback.{u, u + 2, u + 2} (coproductEtale U).hom M q δ = 0 →
        cohomologyPullback.{u, u + 2, u + 2}
          ((baseChangedDiagram R Ω f).obj (op V)).hom M q δ = 0) := by
  let := limitSourceAlgebra R Ω f
  let : Module.Finite (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) :=
    limitSource_moduleFinite R Ω f
  exact exists_finite_pointed_stage_lift R Ω (GeometricEtaleColimit R Ω)
    (limitSourceRing R Ω f) f (limitSourceIso R Ω f) U m (fun i => by
      simpa only [limitResidueMap, finiteSourceResiduePoint,
        limitSourceTargetMap, Category.assoc] using hm i)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
