/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.Colimit
public import Aglib.RingTheory.IntegralClosure.FilteredBaseChange
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Integral closure under the original pointed etale colimit

The existing ring colimit lifts to the under category without changing its
carrier or stage maps. Smooth base change at the actual etale stages and
filtered descent give bijectivity of the original integral-closure comparison.
No smoothness or flatness of the colimit map is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace GeometricEtaleNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The existing pointed stages as rings under their original base. -/
def underDiagram : GeometricEtaleNeighborhood R Ω ⥤ Under (CommRingCat.of R) :=
  diagram R Ω ⋙ (commAlgCatEquivUnder (CommRingCat.of R)).functor

end GeometricEtaleNeighborhood

namespace GeometricEtaleColimit

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]

/-- The unchanged colimit, with its original base map, as a cocone under the base. -/
def underCocone : Cocone (GeometricEtaleNeighborhood.underDiagram R Ω) where
  pt := (CommRingCat.of R).mkUnder (GeometricEtaleColimit R Ω)
  ι.app X := (ι R Ω X).toUnder
  ι.naturality {X Y} f := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (ι_naturality f)

/-- Forgetting the base map gives exactly the already constructed ring cocone. -/
def underCocone_isColimit : IsColimit (underCocone R Ω) := by
  let : IsConnected (GeometricEtaleNeighborhood R Ω) := IsFiltered.isConnected _
  apply isColimitOfReflects (Under.forget (CommRingCat.of R))
  exact ringCoconeIsColimit R Ω

variable (B : Type u) [CommRing B] [Algebra R B]

/-- The original tensor-to-integral-closure map is bijective for the actual
pointed etale colimit. The ambient algebra is arbitrary. -/
theorem toIntegralClosure_bijective :
    Function.Bijective (TensorProduct.toIntegralClosure R (GeometricEtaleColimit R Ω) B) := by
  apply TensorProduct.toIntegralClosure_bijective_of_isColimit
    (CommRingCat.of R) (CommRingCat.of B)
    (GeometricEtaleNeighborhood.underDiagram R Ω) (underCocone R Ω)
    (underCocone_isColimit R Ω)
  intro X
  change @Function.Bijective _ _
    (@TensorProduct.toIntegralClosure R X.algebra _ _
      (algebraMap R X.algebra).toAlgebra B _ _)
  rw [toAlgebra_algebraMap]
  exact TensorProduct.toIntegralClosure_bijective_of_smooth

/-- The comparison equivalence is the original canonical comparison map,
not a newly selected normalization or ambient algebra. -/
def integralClosureEquiv :
    GeometricEtaleColimit R Ω ⊗[R] integralClosure R B ≃ₐ[GeometricEtaleColimit R Ω]
      integralClosure (GeometricEtaleColimit R Ω) (GeometricEtaleColimit R Ω ⊗[R] B) :=
  AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R (GeometricEtaleColimit R Ω) B)
    (toIntegralClosure_bijective R Ω B)

/-- On pure tensors the unchanged comparison retains the original integral element. -/
@[simp] theorem integralClosureEquiv_tmul_val (a : GeometricEtaleColimit R Ω)
    (b : integralClosure R B) :
    (integralClosureEquiv R Ω B (a ⊗ₜ[R] b)).val = a ⊗ₜ[R] (b : B) := rfl

end GeometricEtaleColimit
