/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.StructureScalars
public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Frobenius

/-! # Original scalar and Frobenius maps under Zariski restriction -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- The ring comparison is the native open-subscheme top-section isomorphism. -/
theorem zariskiStructurePresheafIso_app (X : Scheme.{u}) (U : X.Opens) :
    (zariskiStructurePresheafIso X).hom.app (op U) = U.topIso.hom := by
  simp only [zariskiStructurePresheafIso, opensToEtaleForgetIso, Scheme.restrictFunctorΓ,
    Scheme.Opens.topIso, Functor.comp_obj, Functor.op_obj]
  exact Category.id_comp _

/-- The comparison carries restriction of global scalars to their original Zariski restriction. -/
theorem zariskiStructurePresheafIso_appTop (X : Scheme.{u}) (U : X.Opens) :
    U.ι.appTop ≫ (zariskiStructurePresheafIso X).hom.app (op U) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  rw [zariskiStructurePresheafIso_app, Scheme.Opens.ι_appTop]
  simp only [Scheme.Opens.topIso_hom, ← Functor.map_comp]
  congr 1

/-- The exact scalar maps used by the original Zariski and étale cohomology commute. -/
theorem zariskiStructureIso_scalar {k : Type u} [Field k] (Y : FScheme k) (a : k) :
    (zariskiRestriction Y.left).map
        (Curves.structureScalar Y.left (Scheme.constants Y a)) ≫
      (zariskiStructureIso Y.left).hom =
    (zariskiStructureIso Y.left).hom ≫
      (Sheaf.BasisAcyclicity.valueLift.{u,u,u,u+1}
        (Opens.grothendieckTopology Y.left)).map (Scheme.structureScalar Y a) := by
  ext U s
  apply ULift.ext
  change ((zariskiStructurePresheafIso Y.left).hom.app U).hom
      (Mul.mul (α := Γ(U.unop.toScheme, ⊤))
        (U.unop.ι.appTop.hom (Scheme.constants Y a)) s.down) =
    Scheme.constantSection Y U.unop a *
      ((zariskiStructurePresheafIso Y.left).hom.app U).hom s.down
  have h := congrArg (fun q => q.hom (Scheme.constants Y a))
    (zariskiStructurePresheafIso_appTop Y.left U.unop)
  exact (map_mul ((zariskiStructurePresheafIso Y.left).hom.app U).hom
    (show Γ(U.unop.toScheme, ⊤) from U.unop.ι.appTop.hom (Scheme.constants Y a))
    (show Γ(U.unop.toScheme, ⊤) from s.down)).trans
      (congrArg (fun r : Γ(Y.left, U.unop) =>
        r * ((zariskiStructurePresheafIso Y.left).hom.app U).hom s.down) h)

/-- Principal Frobenius restricts to the literal power map on original Zariski sections. -/
theorem zariskiStructureIso_frobenius_apply (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens)
    (s : ((zariskiRestriction X).obj (additiveStructureSheaf X)).obj.obj (op U)) :
    (((zariskiStructureIso X).hom.hom.app (op U))
      ((((zariskiRestriction X).map (structureFrobenius X p hp hX)).hom.app (op U)) s)).down =
    (show Γ(X, U) from (((zariskiStructureIso X).hom.hom.app (op U)) s).down) ^ p := by
  change ((zariskiStructurePresheafIso X).hom.app (op U)).hom
    ((show Γ(U.toScheme, ⊤) from s.down) ^ p) = _
  exact map_pow ((zariskiStructurePresheafIso X).hom.app (op U)).hom
    (show Γ(U.toScheme, ⊤) from s.down) p

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
