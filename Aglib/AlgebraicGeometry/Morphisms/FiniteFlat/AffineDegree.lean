/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree

/-!
# Degree of an affine scheme from its algebra

General declarations relocated from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original namespaces, objects, maps, hypotheses and source boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.AffineDegree` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`aedde6b0da75404ba0eb839efa9ea843023232ae1cbbe9a2a7060ad26ef379a9`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The existing finite scheme degree reduces to the actual algebra dimension
on affine schemes, with the structural scalar map checked explicitly. -/
theorem finiteSchemeDegree_spec (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    finiteSchemeDegree k (Spec.map (CommRingCat.ofHom (algebraMap k A))) = Module.finrank k A := by
  let : Algebra k Γ(Spec (.of A), ⊤) :=
    coordinateAlgebra k (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  change Module.finrank k Γ(Spec (.of A), ⊤) = Module.finrank k A
  let e : Γ(Spec (.of A), ⊤) ≃ₐ[k] A := {
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv with
    commutes' := fun x => by
      have h : (Scheme.ΓSpecIso (.of k)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
          (Scheme.ΓSpecIso (.of A)).hom = CommRingCat.ofHom (algebraMap k A) := by
        rw [Scheme.ΓSpecIso_naturality]
        simp
      exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of A => f x) h }
  exact e.toLinearEquiv.finrank_eq

theorem twoPointSchemeDegree (k : Type u) [Field k] :
    finiteSchemeDegree k (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) = 2 := by
  rw [finiteSchemeDegree_spec]
  simp

end AlgebraicGeometry.Scheme.Hom
