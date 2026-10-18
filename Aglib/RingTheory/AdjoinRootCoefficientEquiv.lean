/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot

/-!
# Coefficient extension of root-algebra equivalences

An actual base-algebra homomorphism between two polynomial root algebras
extends to the literal coefficient-image root algebras. Its extension commutes
with the original root-algebra coefficient maps. Inverses therefore extend to
an actual algebra equivalence, without irreducibility or field assumptions.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k L : Type*} [CommRing k] [CommRing L] [Algebra k L]

/-- The literal coefficient extension on a polynomial root algebra, as a
base-algebra homomorphism. -/
def coefficientMap (p : k[X]) : AdjoinRoot p →ₐ[k] AdjoinRoot (p.map (algebraMap k L)) :=
  mapAlgHom (Algebra.ofId k L) p (p.map (algebraMap k L)) dvd_rfl

@[simp]
theorem coefficientMap_root (p : k[X]) :
    coefficientMap (L := L) p (root p) = root (p.map (algebraMap k L)) :=
  map_root (algebraMap k L) p (p.map (algebraMap k L)) dvd_rfl

/-- Extend an actual root-algebra homomorphism across the coefficient map. -/
def coefficientExtension {p q : k[X]} (f : AdjoinRoot p →ₐ[k] AdjoinRoot q) :
    AdjoinRoot (p.map (algebraMap k L)) →ₐ[L] AdjoinRoot (q.map (algebraMap k L)) :=
  liftAlgHom _ (Algebra.ofId L _) (coefficientMap q (f (root p))) (by
    change aeval (coefficientMap q (f (root p))) (p.map (algebraMap k L)) = 0
    rw [aeval_map_algebraMap, aeval_algHom_apply, aeval_algHom_apply, aeval_eq, mk_self,
      map_zero, map_zero])

@[simp]
theorem coefficientExtension_root {p q : k[X]} (f : AdjoinRoot p →ₐ[k] AdjoinRoot q) :
    coefficientExtension (L := L) f (root (p.map (algebraMap k L))) =
      coefficientMap q (f (root p)) :=
  liftAlgHom_root _ _ _ _

/-- The extended homomorphism commutes on every original root-algebra element. -/
theorem coefficientExtension_coefficientMap {p q : k[X]}
    (f : AdjoinRoot p →ₐ[k] AdjoinRoot q) (x : AdjoinRoot p) :
    coefficientExtension (L := L) f (coefficientMap p x) = coefficientMap q (f x) := by
  have h : ((coefficientExtension (L := L) f).restrictScalars k).comp
      (coefficientMap p) = (coefficientMap q).comp f := by
    apply algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, coefficientMap_root,
      coefficientExtension_root]
  exact AlgHom.congr_fun h x

/-- Literal coefficient extension of an actual root-algebra equivalence. -/
def coefficientEquiv {p q : k[X]} (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) :
    AdjoinRoot (p.map (algebraMap k L)) ≃ₐ[L] AdjoinRoot (q.map (algebraMap k L)) :=
  AlgEquiv.ofAlgHom (coefficientExtension e.toAlgHom) (coefficientExtension e.symm.toAlgHom)
    (by
      apply algHom_ext
      simp only [AlgHom.comp_apply, coefficientExtension_root,
        coefficientExtension_coefficientMap,
        AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, coefficientMap_root, AlgHom.id_apply])
    (by
      apply algHom_ext
      simp only [AlgHom.comp_apply, coefficientExtension_root,
        coefficientExtension_coefficientMap,
        AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, coefficientMap_root, AlgHom.id_apply])

/-- The resulting equivalence extends the specified original equivalence. -/
theorem coefficientEquiv_coefficientMap {p q : k[X]}
    (e : AdjoinRoot p ≃ₐ[k] AdjoinRoot q) (x : AdjoinRoot p) :
    coefficientEquiv (L := L) e (coefficientMap p x) = coefficientMap q (e x) :=
  coefficientExtension_coefficientMap e.toAlgHom x

end AdjoinRoot
