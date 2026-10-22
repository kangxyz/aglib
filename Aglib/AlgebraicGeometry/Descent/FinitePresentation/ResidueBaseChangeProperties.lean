/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ResidueBaseChangeLimit

/-!
# Geometric hypotheses for the actual residue-stage limit

The residue-stage transitions are affine. Quasi-compactness and
quasi-separatedness of the original structural map give the stage-space
hypotheses required by finite-etale object descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeResidueLimit

universe u

open Algebra.FiniteTypeSubalgebraLimit

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (p : Ideal A) [p.IsMaximal] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

instance transition_isAffineHom {s t : (Finset A)ᵒᵖ} (g : s ⟶ t) :
    IsAffineHom ((schemeDiagram R A p f).map g) := by
  apply MorphismProperty.overPullbackMap (P := @IsAffineHom) f
    ((Over.lift (specDiagram R A p) (baseStructure R A p)).map g)
  change IsAffineHom (Spec.map _)
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance stage_compact [QuasiCompact f] (s : (Finset A)ᵒᵖ) :
    CompactSpace ((schemeDiagram R A p f).obj s) := by
  change CompactSpace
    (pullback (Spec.algebraMap R (stagePrime R A p s.unop).ResidueField) f : Scheme)
  exact QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst (Spec.algebraMap R (stagePrime R A p s.unop).ResidueField) f)

set_option backward.isDefEq.respectTransparency.types false in
instance stage_quasiSeparated [QuasiSeparated f] (s : (Finset A)ᵒᵖ) :
    QuasiSeparatedSpace ((schemeDiagram R A p f).obj s) := by
  change QuasiSeparatedSpace
    (pullback (Spec.algebraMap R (stagePrime R A p s.unop).ResidueField) f : Scheme)
  exact quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst (Spec.algebraMap R (stagePrime R A p s.unop).ResidueField) f)

end AlgebraicGeometry.Scheme.FiniteTypeResidueLimit
