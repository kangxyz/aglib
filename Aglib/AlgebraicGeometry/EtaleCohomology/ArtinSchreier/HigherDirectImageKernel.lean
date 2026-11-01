/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.ShortExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Original restricted Artin--Schreier higher-image kernels

The native long exact sequence identifies the original prime-field higher
image with the original Artin--Schreier kernel on the same étale restriction.
Degree zero uses left exactness; positive degrees use only genuine epimorphy
of the preceding restricted original map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

variable {X S T : Scheme.{u}} (f : X ⟶ S) (j : T ⟶ S) [Etale j]
  (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)

local instance : PreservesFiniteColimits (etaleRestriction j) :=
  preservesFiniteColimits_of_natIso (inverseImageEtaleIso j)

local instance : (etaleRestriction j).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The original restricted prime-field higher image is the native kernel
of the restricted original Artin--Schreier map in the next degree. -/
def restrictedPrimeFieldHigherDirectImageKernelIsoSucc (q : ℕ)
    [Epi ((etaleRestriction j).map
      ((higherDirectImage f q).map (artinSchreierMap X p hp hX)))] :
    (etaleRestriction j).obj ((higherDirectImage f (q + 1)).obj (primeFieldSheaf X p)) ≅
      kernel ((etaleRestriction j).map
        ((higherDirectImage f (q + 1)).map (artinSchreierMap X p hp hX))) := by
  let : Epi ((etaleRestriction j).map
      ((higherDirectImage f q).map (artinSchreierComplex X p hp hX).g)) :=
    inferInstanceAs (Epi ((etaleRestriction j).map
      ((higherDirectImage f q).map (artinSchreierMap X p hp hX))))
  exact Functor.rightDerivedKernelIsoOfEpi (directImage f) (etaleRestriction j)
    (artinSchreierComplex X p hp hX) (artinSchreierComplex_shortExact X p hp hX) q

/-- The kernel identification retains the literal original prime-field inclusion. -/
@[reassoc]
theorem restrictedPrimeFieldHigherDirectImageKernelIsoSucc_hom_ι (q : ℕ)
    [Epi ((etaleRestriction j).map
      ((higherDirectImage f q).map (artinSchreierMap X p hp hX)))] :
    (restrictedPrimeFieldHigherDirectImageKernelIsoSucc f j p hp hX q).hom ≫
      kernel.ι ((etaleRestriction j).map
        ((higherDirectImage f (q + 1)).map (artinSchreierMap X p hp hX))) =
      (etaleRestriction j).map
        ((higherDirectImage f (q + 1)).map (primeFieldToStructure X p hX)) := by
  let : Epi ((etaleRestriction j).map
      ((higherDirectImage f q).map (artinSchreierComplex X p hp hX).g)) :=
    inferInstanceAs (Epi ((etaleRestriction j).map
      ((higherDirectImage f q).map (artinSchreierMap X p hp hX))))
  exact Functor.rightDerivedKernelIsoOfEpi_hom_ι (directImage f) (etaleRestriction j)
    (artinSchreierComplex X p hp hX) (artinSchreierComplex_shortExact X p hp hX) q

/-- Degree zero needs no preceding epimorphism assumption. -/
def restrictedPrimeFieldHigherDirectImageKernelIsoZero :
    (etaleRestriction j).obj ((higherDirectImage f 0).obj (primeFieldSheaf X p)) ≅
      kernel ((etaleRestriction j).map
        ((higherDirectImage f 0).map (artinSchreierMap X p hp hX))) :=
  Functor.rightDerivedZeroKernelIso (directImage f) (etaleRestriction j)
    (artinSchreierComplex X p hp hX) (artinSchreierComplex_shortExact X p hp hX)

/-- The degree-zero kernel identification retains the same original inclusion. -/
@[reassoc]
theorem restrictedPrimeFieldHigherDirectImageKernelIsoZero_hom_ι :
    (restrictedPrimeFieldHigherDirectImageKernelIsoZero f j p hp hX).hom ≫
      kernel.ι ((etaleRestriction j).map
        ((higherDirectImage f 0).map (artinSchreierMap X p hp hX))) =
      (etaleRestriction j).map
        ((higherDirectImage f 0).map (primeFieldToStructure X p hX)) :=
  Functor.rightDerivedZeroKernelIso_hom_ι (directImage f) (etaleRestriction j)
    (artinSchreierComplex X p hp hX) (artinSchreierComplex_shortExact X p hp hX)

end AlgebraicGeometry.Scheme.EtaleCohomology
