/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # Recovering an original cover from a section and its retraction

The candidate is the actual geometric pullback of the original section cover.
It is finite etale by base change, independently of any later global-section
algebra. The original composition and identity comparisons fix the recovered
isomorphism on the section.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable {U V : Scheme.{u}} (s : U ⟶ V) (t : V ⟶ U) (h : s ≫ t = 𝟙 U)

/-- The canonical section comparison for the actual iterated pullback. -/
def sectionRetractionComparison (D : FiniteEtale V) :
    (baseChange s).obj ((baseChange t).obj ((baseChange s).obj D)) ≅
      (baseChange s).obj D :=
  (baseChangeComp t s).symm.app ((baseChange s).obj D) ≪≫
    (eqToIso (congrArg baseChange h)).app ((baseChange s).obj D) ≪≫
      (baseChangeId U).app ((baseChange s).obj D)

/-- Full faithfulness on the actual section recovers the original cover
from the actual geometric pullback of its section restriction. -/
def coverIsoOfFullyFaithfulSection (hs : (baseChange s).FullyFaithful)
    (D : FiniteEtale V) :
    D ≅ (baseChange t).obj ((baseChange s).obj D) :=
  hs.preimageIso (sectionRetractionComparison s t h D).symm

/-- The recovered isomorphism restricts to the prescribed original section
comparison, rather than an arbitrarily chosen isomorphism of section covers. -/
@[simp]
theorem coverIsoOfFullyFaithfulSection_map_hom
    (hs : (baseChange s).FullyFaithful) (D : FiniteEtale V) :
    (baseChange s).map (coverIsoOfFullyFaithfulSection s t h hs D).hom =
      (sectionRetractionComparison s t h D).inv := by
  simp [coverIsoOfFullyFaithfulSection, Functor.FullyFaithful.preimageIso]

/-- The inverse has the original forward comparison on the same section. -/
@[simp]
theorem coverIsoOfFullyFaithfulSection_map_inv
    (hs : (baseChange s).FullyFaithful) (D : FiniteEtale V) :
    (baseChange s).map (coverIsoOfFullyFaithfulSection s t h hs D).inv =
      (sectionRetractionComparison s t h D).hom := by
  simp [coverIsoOfFullyFaithfulSection, Functor.FullyFaithful.preimageIso]

end AlgebraicGeometry.Scheme.FiniteEtale
