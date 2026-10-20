/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent

/-!
# Finite presentation of actual line bundles

The original arbitrary-scheme lemma is relocated unchanged from
`R5Lab.AlgebraicGeometry.Curves.RiemannRoch` at R5 source basis
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Its namespace, singleton local
bases, finite-presentation object, universes, hypotheses and proof are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`ed253c07b9ff94a308fb71a34c569d53f3067815e19bcc94348115d37f775dab`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (finitePresentation_of_finite_local_basis)
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u

theorem lineBundle_isFinitePresentation (X : Scheme.{u}) (L :
    Scheme.Modules.Invertible.LineBundle X) :
    L.val.IsFinitePresentation := by
  obtain ⟨q, hq, hI⟩ := L.property
  let := hq
  let (i : q.I) : Finite (q.generators i).I := Finite.of_equiv PUnit (hI i).some.symm
  exact finitePresentation_of_finite_local_basis X L.val q

end AlgebraicGeometry.Scheme.Modules.Invertible
