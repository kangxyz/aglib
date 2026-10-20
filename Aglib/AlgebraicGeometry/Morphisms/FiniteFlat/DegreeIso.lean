/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree

/-!
# Global-section degree under a structural scheme isomorphism

Extracted from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original declaration names, mathematical hypotheses, and source boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeIso` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`5c5c2bf2a795932368917dc5cedde63dc678123e23fefc97f2a224b032757d32`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-scheme degree is invariant under the actual structural isomorphism.
The induced algebra equivalence uses the actual structural scalar maps. -/
theorem finiteSchemeDegree_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of k)) (e : X ≅ Y)
    (he : e.hom ≫ q = p) : AlgebraicGeometry.Scheme.Hom.finiteSchemeDegree k p =
        AlgebraicGeometry.Scheme.Hom.finiteSchemeDegree k q := by
  let : Algebra k Γ(X, ⊤) := coordinateAlgebra k (Over.mk p)
  let : Algebra k Γ(Y, ⊤) := coordinateAlgebra k (Over.mk q)
  let a : Γ(Y, ⊤) ≃ₐ[k] Γ(X, ⊤) := {
    (asIso e.hom.appTop).commRingCatIsoToRingEquiv with
    commutes' := fun x => by
      have h : (Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ e.hom.appTop =
          (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop := by
        rw [← Scheme.Hom.comp_appTop, he]
      exact congrArg (fun f : CommRingCat.of k ⟶ Γ(X, ⊤) => f x) h }
  exact a.toLinearEquiv.finrank_eq.symm


end AlgebraicGeometry.Scheme.Hom
