/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Integral dominant sources over Dedekind affine bases

The original stalk maps are injective. Their targets are torsion-free modules
over the actual Dedekind localizations, hence the original morphism is flat.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A quasi-compact dominant morphism from an integral scheme to the spectrum
of a Dedekind domain is flat, through its original stalk maps. -/
theorem flat_of_isIntegral_of_isDominant {A : Type u} [CommRing A] [IsDedekindDomain A]
    {Z : Scheme.{u}} [IsIntegral Z] (p : Z ⟶ Spec (.of A)) [QuasiCompact p] [IsDominant p] :
    Flat p := by
  have : IsSchemeTheoreticallyDominant p := IsSchemeTheoreticallyDominant.of_isDominant p
  apply Flat.of_stalkMap
  intro z
  have hinj : Function.Injective (p.stalkMap z).hom := by
    apply stalkMap_injective_of_isAffine p z
    intro a ha
    rw [TopCat.Presheaf.Γgerm, Scheme.Hom.germ_stalkMap_apply] at ha
    have hzero : p.app ⊤ a = 0 :=
      (germ_injective_of_isIntegral Z z (show z ∈ p ⁻¹ᵁ ⊤ from trivial))
        (by simpa only [map_zero] using ha)
    have ha0 : a = 0 := (p.app_injective ⊤) (by simpa only [map_zero] using hzero)
    simp [ha0]
  let B := (Spec (.of A)).presheaf.stalk (p z)
  have : (p z).asIdeal.IsPrime := (p z).isPrime
  let : Algebra A B := inferInstanceAs
    (Algebra A ((Spec.structureSheaf A).presheaf.stalk (p z)))
  have : IsLocalization.AtPrime B (p z).asIdeal := inferInstanceAs
    (IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk (p z)) (p z).asIdeal)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B
    (p z).asIdeal.primeCompl_le_nonZeroDivisors
  have : IsDedekindDomain B := IsLocalization.AtPrime.isDedekindDomain A (p z).asIdeal B
  let : Algebra B (Z.presheaf.stalk z) := (p.stalkMap z).hom.toAlgebra
  have : Module.IsTorsionFree B (Z.presheaf.stalk z) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end AlgebraicGeometry.Scheme.Hom
