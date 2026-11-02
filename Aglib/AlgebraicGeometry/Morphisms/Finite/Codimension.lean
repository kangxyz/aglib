/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.FunctionField
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.RingTheory.KrullDimension.IntegralExtension

/-! # Codimension under an original finite dominant morphism

Normality of the target supplies going down on the actual affine section map.
The source chart is the entire original inverse image of the target chart.
No Noetherianity, source normality, or new local or generic model is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A finite dominant morphism between integral schemes with normal target
preserves the coheight of every original point. -/
theorem coheight_eq_of_finite_of_normal {Y X : Scheme.{u}}
    [IsIntegral Y] [IsIntegral X] (q : Y ⟶ X) [IsFinite q] [IsDominant q]
    (hX : NormalStalks X) (z : Y) : Order.coheight (q z) = Order.coheight z := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hz, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (q z)) isOpen_univ
  let : Nonempty U := ⟨⟨q z, hz⟩⟩
  let : Nonempty (q ⁻¹ᵁ U) := ⟨⟨z, hz⟩⟩
  let hV := hU.preimage q
  let := LocalNormAlgebra.chartAlgebra q U
  let := LocalNormAlgebra.chart_finite q U hU
  let : FaithfulSMul Γ(X, U) Γ(Y, q ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (LocalNormAlgebra.chartMap_injective q U)
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  let := Scheme.isIntegrallyClosed_sections_of_isAffineOpen X U hU
  have hc : (hV.primeIdealOf ⟨z, hz⟩).asIdeal.under Γ(X, U) =
      (hU.primeIdealOf ⟨q z, hz⟩).asIdeal := by
    change (hV.primeIdealOf ⟨z, hz⟩).asIdeal.comap (q.app U).hom = _
    exact congrArg PrimeSpectrum.asIdeal (by
      simpa only [Hom.appLE_eq_app] using
        IsAffineOpen.comap_primeIdealOf_appLE U hU (q ⁻¹ᵁ U) hV le_rfl hz)
  have hh := Ideal.height_eq_height_under_of_normal
    (R := Γ(X, U)) (hV.primeIdealOf ⟨z, hz⟩).asIdeal
  rw [hc, idealHeight_eq_coheight, idealHeight_eq_coheight] at hh
  have hs := coheight_eq_of_isOpenImmersion (x := hV.primeIdealOf ⟨z, hz⟩) hV.fromSpec
  have ht := coheight_eq_of_isOpenImmersion (x := hU.primeIdealOf ⟨q z, hz⟩) hU.fromSpec
  rw [hV.fromSpec_primeIdealOf] at hs
  rw [hU.fromSpec_primeIdealOf] at ht
  exact ht.trans (hh.symm.trans hs.symm)

end AlgebraicGeometry.Scheme.Hom
