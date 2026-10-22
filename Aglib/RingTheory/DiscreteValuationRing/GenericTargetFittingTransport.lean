/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.GenericTargetSquare
public import Aglib.RingTheory.NeronModification.EvaluatedFittingBaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability

/-! # Fitting transport along the actual generic source and target

The actual tensor source, actual `tensorTarget`, and actual target coefficient
map are used throughout. The modification theorem retains the original finite
centre family and proves its target square by regularity.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.NeronModification

namespace GenericParameterCentre

variable {R S B ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [CommRing B] [Algebra R B] [Finite ι]
  (p : R) [Fact (Irreducible p)] [Fact (Irreducible (algebraMap R S p))]
  (χ : B →ₐ[R] S)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "R₁" => ParameterLocalization.Ring R ι p
local notation "S₁" => ParameterLocalization.Ring S ι (algebraMap R S p)
local notation "B₁" => B ⊗[R] R₁

/-- The actual tensor target square on the original source coefficients. -/
theorem tensorTarget_comp_algebraMap :
    (tensorTarget R S ι p χ).toRingHom.comp (algebraMap B B₁) =
      (algebraMap S S₁).comp χ.toRingHom := by
  ext b
  change tensorTarget R S ι p χ (b ⊗ₜ[R] (1 : R₁)) = algebraMap S S₁ (χ b)
  rw [tensorTarget_tmul, map_one, mul_one]

/-- The original evaluated differential Fitting ideal extends along the actual
target map `S → S₁`, with no change of Fitting index. -/
theorem map_fittingIdeal_tensorTarget
    [Module.Finite B (KaehlerDifferential R B)] (k : ℕ) :
    (Module.fittingIdeal B₁ (KaehlerDifferential R₁ B₁) k).map
      (tensorTarget R S ι p χ).toRingHom =
    ((Module.fittingIdeal B (KaehlerDifferential R B) k).map χ.toRingHom).map
      (algebraMap S S₁) := by
  exact KaehlerDifferential.map_fittingIdeal_of_isPushout R R₁ B B₁
    χ.toRingHom (tensorTarget R S ι p χ).toRingHom (algebraMap S S₁)
    (tensorTarget_comp_algebraMap p χ) k

/-- The SAME original modification has the same evaluated Fitting transport.
Only the actual restrictions of the two modification points are inputs. -/
theorem map_fittingIdeal_tensorTarget_modification
    {ν : Type*} [Finite ν] [Algebra.FiniteType R B] (g : ν → B)
    (χM : Modification (algebraMap R B p) g →+* S)
    (χN : Modification (algebraMap B B₁ (algebraMap R B p))
      (fun j => algebraMap B B₁ (g j)) →+* S₁)
    (hχM : χM.comp (of (algebraMap R B p) g) = χ.toRingHom)
    (hχN : χN.comp (of (algebraMap B B₁ (algebraMap R B p))
      (fun j => algebraMap B B₁ (g j))) = (tensorTarget R S ι p χ).toRingHom)
    (k : ℕ) :
    (Module.fittingIdeal _ (KaehlerDifferential R₁
      (Modification (algebraMap B B₁ (algebraMap R B p))
        (fun j => algebraMap B B₁ (g j)))) k).map χN =
    ((Module.fittingIdeal _ (KaehlerDifferential R
      (Modification (algebraMap R B p) g)) k).map χM).map (algebraMap S S₁) := by
  let : Module.Flat R R₁ := inferInstance
  let : Module.Flat B B₁ := inferInstance
  have hregular : IsRegular (algebraMap S S₁ (χ.toRingHom (algebraMap R B p))) := by
    change IsRegular (algebraMap S S₁ (χ (algebraMap R B p)))
    rw [χ.commutes]
    exact isRegular_iff_ne_zero.mpr
      (ParameterLocalization.uniformizer_irreducible S ι (algebraMap R S p)).ne_zero
  exact map_fittingIdeal_baseChangeOriginal (R := R) (R' := R₁) (B' := B₁)
    (algebraMap R B p) g χ.toRingHom (tensorTarget R S ι p χ).toRingHom
    (algebraMap S S₁) (tensorTarget_comp_algebraMap p χ) χM χN hχM hχN hregular k

end GenericParameterCentre
