/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.LocalBaseResidue
public import Aglib.AlgebraicGeometry.FunctionField.StalkInjection
public import Aglib.AlgebraicGeometry.Morphisms.FiniteType.ResidueField
public import Aglib.RingTheory.AdicCompletion.NormalSurface
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Normal completion of an original stalk over a complete surface base

Properness sends the original closed point to the original local closed
point. The native closed-base stalk and residue comparisons identify the
actual scalar map; dominance proves injection and finite type proves the
finite original residue extension. The ring completion theorem then applies
to the same original stalk. No selected stalk is assumed finite or complete,
and no birationality or global dimension bound is required.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed normal dimension-two Nagata stalk on an actual proper dominant
model over a complete local domain of dimension two has normal-domain
completion. The complete base need not separately be Noetherian or normal. -/
theorem normalDomain_completion_stalk_of_complete_surface
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hdA : ringKrullDim A = 2) (x : X) (hx : IsClosed ({x} : Set X))
    (hN : IsIntegrallyClosed (X.presheaf.stalk x))
    (hdx : ringKrullDim (X.presheaf.stalk x) = 2)
    (hNagata : IsNagataRing.{u, 0} (X.presheaf.stalk x)) :
    IsDomain (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) ∧
      IsIntegrallyClosed
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) := by
  let T := X.presheaf.stalk x
  let : IsIntegrallyClosed T := hN
  let : IsNoetherianRing T := hNagata.isNoetherianRing
  have hfx : f x = closedPoint A := by
    have hc : IsClosed ({f x} : Set (Spec (.of A))) := by
      simpa only [Set.image_singleton] using f.isClosedMap {x} hx
    have hm : (f x).asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f x)).mp hc
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal hm
  let : Algebra A T := (f.stalkScalar x).toAlgebra
  let : IsLocalHom (algebraMap A T) := f.stalkScalar_isLocalHom_of_closedPoint x hfx
  have hinjStalk : Function.Injective (f.stalkMap x).hom :=
    f.stalkMap_injective_of_isDominant x
  have hinj : Function.Injective (algebraMap A T) := by
    have h := hinjStalk.comp (f.closedBaseStalkEquiv x hfx).injective
    change Function.Injective
      ((f.stalkMap x).hom.comp (f.closedBaseStalkEquiv x hfx).toRingHom) at h
    rw [f.closedBaseStalkEquiv_stalkMap x hfx] at h
    exact h
  have hres : (ResidueField.map (f.stalkScalar x)).Finite :=
    (f.stalkScalar_residueMap_finite_iff x hfx).mpr
      (f.residueFieldMap_finite_of_closedPoint x hx)
  have he : algebraMap (ResidueField A) (ResidueField T) =
      ResidueField.map (f.stalkScalar x) := by
    apply RingHom.ext
    intro z
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
    rfl
  let : Module.Finite (ResidueField A) (ResidueField T) := by
    apply RingHom.finite_algebraMap.mp
    rw [he]
    exact hres
  exact AdicCompletion.normalDomain_of_complete_normal_surface A T hinj hdA hdx hNagata

end AlgebraicGeometry.Scheme.Hom
