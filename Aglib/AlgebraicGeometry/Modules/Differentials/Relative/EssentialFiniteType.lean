/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FiniteType
public import Mathlib.RingTheory.RingHom.EssFiniteType


/-!
# Original differentials over an essentially finite-type coefficient map

A finite-type scheme over the actual local coefficient ring has finite
relative differentials over the original coefficient ring. The composite
scheme map is not asserted to be locally of finite type.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

open Scheme.Modules Scheme.Modules.Differentials

variable {Λ R T : CommRingCat.{u}} {X : Scheme.{u}}
  (ρ : Λ ⟶ R) (b : X ⟶ Spec R) (j : Spec T ⟶ X)

/-- The chart coefficient map is the original coefficient map followed by
its actual chart structure map. -/
theorem differentialChartCoefficient_comp :
    Spec.preimage (j ≫ (b ≫ Spec.map ρ)) = ρ ≫ Spec.preimage (j ≫ b) := by
  apply Spec.map_injective
  rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Category.assoc]

/-- Essential finite type of the actual base coefficient map suffices for
finiteness of the original chart Kähler module. -/
theorem finite_kaehler_of_essFiniteType (hρ : ρ.hom.EssFiniteType)
    [LocallyOfFiniteType b] [IsOpenImmersion j] :
    Module.Finite T (CommRingCat.KaehlerDifferential
      (Spec.preimage (j ≫ (b ≫ Spec.map ρ)))) := by
  let σ := Spec.preimage (j ≫ b)
  have hσ : LocallyOfFiniteType (Spec.map σ) :=
    (Spec.map_preimage (j ≫ b)).symm ▸
      (inferInstance : LocallyOfFiniteType (j ≫ b))
  have hfinite : σ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hσ
  rw [differentialChartCoefficient_comp]
  let τ : Λ ⟶ T := ρ ≫ σ
  have hτ : τ.hom.EssFiniteType := hρ.comp hfinite.essFiniteType
  let : Algebra Λ T := τ.hom.toAlgebra
  let : Algebra.EssFiniteType Λ T := hτ
  change Module.Finite T (_root_.KaehlerDifferential Λ T)
  infer_instance

/-- The same original relative differential sheaf is affine-locally finite.
No finite-type assertion is made for the composite to the initial base. -/
theorem relativeDifferentialSheaf_affineLocallyFiniteType_of_essFiniteType
    (hρ : ρ.hom.EssFiniteType) [LocallyOfFiniteType b] :
    affineLocallyFiniteType X (relativeDifferentialSheaf (b ≫ Spec.map ρ)) := by
  intro T j _
  let K : ModuleCat.{u} T :=
    CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ (b ≫ Spec.map ρ)))
  let : Module.Finite T K := finite_kaehler_of_essFiniteType ρ b j hρ
  have hK : affineFiniteSheaf T (tilde K) :=
    ⟨inferInstance, Module.Finite.equiv (tilde.isoTop K).toLinearEquiv⟩
  exact (affineFiniteSheaf T).prop_of_iso
    (relativeDifferentialAffineChartIso (b ≫ Spec.map ρ) j).symm hK

end AlgebraicGeometry.Scheme.Modules.Differentials
