/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Retract
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/VectorBundle/TensorLocalExactness.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 48]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Exact tensor with finite locally free module sheaves

Use the original open-restriction tensor comparison and affine basis cover.
The actual affine finite-free retractions prove local exactness, which the
original restriction functors reflect back to the scheme.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules
/-- The original tensor with an arbitrary finite locally free coefficient
preserves short exactness. -/
theorem tensor_shortExact_finiteLocallyFree {X : Scheme.{u}} (M : X.Modules)
    [IsFiniteLocallyFree X M] (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTensorLeftFunctor X M)).ShortExact := by
  apply shortExact_of_restrict_openCover X.affineBasisCover.X X.affineBasisCover.f
    (fun x => ⟨X.affineBasisCover.idx x, X.affineBasisCover.covers x⟩)
  intro i
  let j := X.affineBasisCover.f i
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (X.affineBasisCover.f i))
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let R := X.affineBasisCoverRing i
  have hres : (S.map (Scheme.Modules.restrictFunctor j)).ShortExact := hS.map _
  have hm : IsFiniteLocallyFree (Spec R) (M.restrict j) := inferInstance
  obtain ⟨I, hI, ⟨r⟩⟩ := exists_retract_finiteFree R (M.restrict j)
  let := hI
  let S' : ShortComplex (Spec R).Modules := S.map (Scheme.Modules.restrictFunctor j)
  have ht : (S'.map (moduleTensorLeftFunctor (Spec R) (M.restrict j))).ShortExact :=
    SheafOfModulesOfCommRing.tensor_shortExact_of_retract_finiteFree
      (Spec R).sheaf S' hres I r
  exact ShortComplex.shortExact_of_iso (S.mapNatIso (tensorRestrictionNatIso j M)) ht

instance moduleTensorLeft_preservesHomology {X : Scheme.{u}} (E : X.Modules)
    [IsFiniteLocallyFree X E] : (moduleTensorLeftFunctor X E).PreservesHomology :=
  ((Functor.exact_tfae (moduleTensorLeftFunctor X E)).out 1 3).mp
    (tensor_shortExact_finiteLocallyFree E)

instance moduleTensorRight_preservesHomology {X : Scheme.{u}} (M : X.Modules)
    [IsFiniteLocallyFree X M] : (moduleTensorRightFunctor X M).PreservesHomology := by
  let : PreservesFiniteLimits (moduleTensorLeftFunctor X M) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits (moduleTensorLeftFunctor X M) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let : PreservesFiniteLimits (moduleTensorRightFunctor X M) :=
    preservesFiniteLimits_of_natIso (moduleTensorRightLeftIso X M).symm
  let : PreservesFiniteColimits (moduleTensorRightFunctor X M) :=
    preservesFiniteColimits_of_natIso (moduleTensorRightLeftIso X M).symm
  infer_instance
end AlgebraicGeometry.Scheme.Modules
