/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finiteness of relative normalization from a schematically dense source

Injectivity of the original section maps embeds each original integral
closure into the finite integral closure of a schematically dense source.
Noetherianity makes this actual submodule finite. No birationality,
normality, reducedness, or integrality of either source is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Finiteness of relative normalization descends along a qcqs
schematically dominant change of source over a locally Noetherian base. -/
theorem isFinite_fromNormalization_of_comp
    {Z V X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : V ⟶ X) (h : Z ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact h] [QuasiSeparated h]
    [IsSchemeTheoreticallyDominant h] [IsFinite (h ≫ f).fromNormalization] :
    IsFinite f.fromNormalization := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra Γ(X, U) Γ(V, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(Z, (h ≫ f) ⁻¹ᵁ U) := ((h ≫ f).app U).hom.toAlgebra
  let φ : Γ(V, f ⁻¹ᵁ U) →ₐ[Γ(X, U)] Γ(Z, (h ≫ f) ⁻¹ᵁ U) :=
    { toRingHom := (h.app (f ⁻¹ᵁ U)).hom
      commutes' _ := rfl }
  have hfinite : (CommRingCat.ofHom (algebraMap Γ(X, U)
      (integralClosure Γ(X, U) Γ(Z, (h ≫ f) ⁻¹ᵁ U)))).hom.Finite := by
    have hc := (RingHom.Finite.of_surjective
      ((h ≫ f).normalizationObjIso hU).hom.hom
      (ConcreteCategory.bijective_of_isIso ((h ≫ f).normalizationObjIso hU).hom).2).comp
        ((h ≫ f).fromNormalization.finite_app U hU)
    change (((h ≫ f).fromNormalization.app U) ≫
      ((h ≫ f).normalizationObjIso hU).hom).hom.Finite at hc
    simpa only [fromNormalization_app _ hU, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using hc
  let : Module.Finite Γ(X, U)
      (integralClosure Γ(X, U) Γ(Z, (h ≫ f) ⁻¹ᵁ U)) :=
    RingHom.finite_algebraMap.mp hfinite
  let : Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(V, f ⁻¹ᵁ U)) :=
    Module.Finite.of_injective φ.mapIntegralClosure.toLinearMap (by
      intro a b hab
      apply Subtype.ext
      apply h.app_injective (f ⁻¹ᵁ U)
      exact congrArg Subtype.val hab)
  rw [fromNormalization_app _ hU]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2).comp
      (RingHom.finite_algebraMap.mpr inferInstance)

end AlgebraicGeometry.Scheme.Hom
