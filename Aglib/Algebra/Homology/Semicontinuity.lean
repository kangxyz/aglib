/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Semicontinuity
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Functor

/-!
# Upper semicontinuity of original fibre-complex homology

For a module complex of any shape, finite terms and finitely presented flat
terms give upper semicontinuity of every residue-field homology dimension.
The comparison uses the original native scalar-extension complex. In a
fixed degree, only finiteness of that term and finite-presentation flatness
of the next term are required. No boundedness or Noetherianity is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module

namespace HomologicalComplex

universe u v w

variable {R : Type u} [CommRing R] {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{max u v} R) c)

/-- The homology dimension of the original scalar-extended residue-field complex is
upper semicontinuous in every degree, under the indicated local term hypotheses. -/
theorem upperSemicontinuous_finrank_homology_residueField (i : ι)
    [Module.Finite R (K.X i)] [Module.FinitePresentation R (K.X (c.next i))]
    [Module.Flat R (K.X (c.next i))] :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          c).obj K).homology i)) := by
  let : Module.Finite R (K.sc i).X₂ := by
    change Module.Finite R (K.X i)
    infer_instance
  let : Module.FinitePresentation R (K.sc i).X₃ := by
    change Module.FinitePresentation R (K.X (c.next i))
    infer_instance
  let : Module.Flat R (K.sc i).X₃ := by
    change Module.Flat R (K.X (c.next i))
    infer_instance
  exact (K.sc i).upperSemicontinuous_finrank_homology_residueField

/-- In particular, every fibre-homology dimension of a complex of finite projective
modules is upper semicontinuous, without any boundedness or Noetherian hypothesis. -/
theorem upperSemicontinuous_finrank_homology_residueField_of_projective
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)] (i : ι) :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          c).obj K).homology i)) := by
  let : Module.FinitePresentation R (K.X (c.next i)) :=
    Module.finitePresentation_of_projective R (K.X (c.next i))
  exact K.upperSemicontinuous_finrank_homology_residueField i

end HomologicalComplex
