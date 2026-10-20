/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.Residue
public import Aglib.AlgebraicGeometry.RationalPoint.Completion

/-!
# Finite-etale fullness at a completed rational-point stalk
-/

@[expose] public section


noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme.RationalPoint.Completion
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
universe u
variable {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
  (q : RationalPoint F X) [IsDiscreteValuationRing q.localRing]

/-- The actual marked closed-fibre functor for the completed rational stalk is full. -/
theorem closed_finiteEtale_full :
    (baseChange (Spec.map (CommRingCat.ofHom
      ((residueEquiv q).toRingHom.comp (IsLocalRing.residue (Ring q)))))).Full :=
  AlgebraicGeometry.Scheme.FiniteEtale.Adic.marked_closed_full
    (Ring q) (residueEquiv q)

end AlgebraicGeometry.Scheme.RationalPoint.Completion

/- Migration source:
R5Lab/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/Adic/RationalPointCompletion.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 495353dd3da05fe5ca2cc7b7828a52ece181cac2d6fc38d47bb55a0bb95959b0.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
