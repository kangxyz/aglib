/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Support

/-!
# Closed support of finite-type quasicoherent sheaves

The ordinary stalk support of an affine-locally finite-type quasicoherent sheaf is closed on an
arbitrary scheme.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/ClosedSupport.lean`.
SHA-256: `aa97ec4260a6f2708476c7b5f2d19dd2d7a7419f132e1452e942db748e4e2fd2`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- The ordinary stalk support of a sheaf satisfying the actual affine-local
finite quasicoherent condition is closed. -/
theorem isClosed_support_of_affineLocallyFiniteType
    {X : Scheme.{u}} {M : X.Modules} (hM : affineLocallyFiniteType
  X M) :
    IsClosed (AlgebraicGeometry.Scheme.Modules.support M) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let i := X.affineOpenCover.idx x
  let j := X.affineOpenCover.f i
  obtain ⟨y, hy⟩ := X.affineOpenCover.covers x
  have hC := hM (X.affineOpenCover.X i) j
  have : ((Scheme.Modules.restrictFunctor j).obj M).IsQuasicoherent := hC.1
  have : Module.Finite (X.affineOpenCover.X i)
      (moduleSpecΓFunctor.obj ((Scheme.Modules.restrictFunctor j).obj M)) := hC.2
  have hc : IsClosed (j ⁻¹' AlgebraicGeometry.Scheme.Modules.support M) := by
    rw [← AlgebraicGeometry.Scheme.Modules.support_restrict j M]
    exact AlgebraicGeometry.Scheme.Modules.isClosed_support_of_finite_globalSections _
  have ho : IsOpen (j '' (j ⁻¹' AlgebraicGeometry.Scheme.Modules.support M)ᶜ) :=
    j.isOpenEmbedding.isOpenMap _ hc.isOpen_compl
  apply Filter.mem_of_superset (ho.mem_nhds ?_) ?_
  · refine ⟨y, ?_, hy⟩
    change j y ∉ AlgebraicGeometry.Scheme.Modules.support M
    rw [show j y = x from hy]
    exact hx
  · rintro z ⟨w, hw, rfl⟩
    exact hw

/-- The actual affine-local finite-type sheaf objects have closed support on every scheme;
no noetherian hypothesis is needed for this support statement. -/
theorem finiteType_support_isClosed {X : Scheme.{u}} (M : FiniteTypeSheaves X)
  :
    IsClosed (AlgebraicGeometry.Scheme.Modules.support M.obj) :=
  isClosed_support_of_affineLocallyFiniteType M.property

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
