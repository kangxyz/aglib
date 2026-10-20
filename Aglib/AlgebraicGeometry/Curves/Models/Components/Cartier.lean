/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Aglib.AlgebraicGeometry.Stalk.FlatDVR.ComponentKernelProof
public import Aglib.RingTheory.Ideal.HeightOne
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Interfaces

/-!
# Cartier ideals of actual vertical components

An integral closed component of the literal residue fibre has height-one
stalk kernels in a locally Noetherian flat scheme over a DVR. The canonical
proved component-kernel supplier gives the actual uniformizer minimal prime.
The codimension-one Cartier family and pointwise regularity remain explicit
when constructing the actual negative component line bundle.

Source: frozen R5 `LocalModels/Incidence/Cartier.lean:103–137`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`. Actual schemes and maps replace the
terminal model wrapper; the original Cartier premise is retained.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.Cartier
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]

/-- The kernel at each stalk of the actual component immersion has height one. -/
theorem component_stalkKernel_height_one {C : Scheme.{u}} [IsIntegral C]
    (i : C ⟶ obj π) [IsClosedImmersion i]
    (hi : Set.range i ∈ irreducibleComponents (obj π)) (c : C) :
    (RingHom.ker ((i ≫ projection π).stalkMap c).hom).height = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨hnzd, hmin⟩ := Scheme.FlatDVR.flatDVRFibreComponentKernel
    R Y C π i ϖ inferInstance inferInstance hi hϖ c
  exact Ideal.minimalPrime_height_one hnzd hmin

/-- The actual component ideal is invertible under the original regular Cartier input. -/
theorem component_ideal_invertible (hcartier : RegularCodimOneIdealInvertible.{u})
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ obj π) [IsClosedImmersion i]
    (hi : Set.range i ∈ irreducibleComponents (obj π)) :
    IsLocallyRankOne Y (idealModule (i ≫ projection π)) :=
  hcartier Y C (i ≫ projection π) inferInstance hregular
    (component_stalkKernel_height_one π i hi)

/-- The actual negative component bundle on the original scheme. -/
def componentIdealLineBundle (hcartier : RegularCodimOneIdealInvertible.{u})
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ obj π) [IsClosedImmersion i]
    (hi : Set.range i ∈ irreducibleComponents (obj π)) : LineBundle Y :=
  ⟨idealModule (i ≫ projection π), component_ideal_invertible π hcartier hregular i hi⟩

@[simp] theorem componentIdealLineBundle_val (hcartier : RegularCodimOneIdealInvertible.{u})
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ obj π) [IsClosedImmersion i]
    (hi : Set.range i ∈ irreducibleComponents (obj π)) :
    (componentIdealLineBundle π hcartier hregular i hi).val =
      idealModule (i ≫ projection π) := rfl

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
