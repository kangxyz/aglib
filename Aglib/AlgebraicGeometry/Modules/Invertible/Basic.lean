/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Line bundles as locally rank-one module sheaves

A line bundle is an actual structure-module sheaf with local free bases
indexed by singleton types. `LineBundleClass` quotients these objects by actual
module-sheaf isomorphism. The trivial bundle and transport of local rank one
under isomorphism are constructed here. Tensor objects and maps are supplied by
the lower scheme tensor owner, which specializes the shared generic site construction.
Tensor closure, associativity and dual inverses are supplied by the following
modules.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.Basic`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
The primary namespace is `AlgebraicGeometry.Scheme.Modules.Invertible`;
source names are provenance.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable (X : Scheme.{u})

/-- Locally free rank one means actual local bases indexed by singleton types. -/
def IsLocallyRankOne (M : SheafOfModules.{u} X.ringCatSheaf) : Prop :=
  ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧
    ∀ i, Nonempty ((q.generators i).I ≃ PUnit.{u + 1})

/-- Actual line bundles on the scheme, before tensor-group construction. -/
def LineBundle := {M : SheafOfModules.{u} X.ringCatSheaf // IsLocallyRankOne X M}

/-- Isomorphism of the underlying actual structure-module sheaves. -/
def lineBundleSetoid : Setoid (LineBundle X) where
  r L M := Nonempty (L.val ≅ M.val)
  iseqv := ⟨fun L => ⟨Iso.refl L.val⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- Isomorphism classes of actual locally rank-one sheaves; tensor laws remain separate. -/
def LineBundleClass := Quotient (lineBundleSetoid X)

/-- The rank-one free structure-module sheaf is a line bundle. -/
def trivialLineBundle : LineBundle X := by
  refine ⟨SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}, ?_⟩
  refine ⟨
    (SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf) PUnit.{u + 1}).localGeneratorsData,
    inferInstance, ?_⟩
  intro i
  exact ⟨Equiv.refl _⟩

/-- Actual locally rank-one objects are locally free in the existing sheaf library. -/
theorem lineBundle_isLocallyFree (L : LineBundle X) : L.val.IsLocallyFree := by
  obtain ⟨q, hq, _⟩ := L.property
  let := hq
  exact q.isLocallyFree

/-- Equality of classes is precisely actual module-sheaf isomorphism. -/
theorem class_eq_iff (L M : LineBundle X) :
    Quotient.mk (lineBundleSetoid X) L = Quotient.mk (lineBundleSetoid X) M ↔
      Nonempty (L.val ≅ M.val) := Quotient.eq

/-- Local rank one is invariant under actual module-sheaf isomorphisms. -/
theorem isLocallyRankOne_of_iso {M N : SheafOfModules.{u} X.ringCatSheaf} (e : M ≅ N)
    (h : IsLocallyRankOne X M) : IsLocallyRankOne X N := by
  obtain ⟨q, hq, hr⟩ := h
  let := hq
  let q' : N.LocalGeneratorsData.{u} := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators i := (q.generators i).ofEpi
      ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).map e.hom) }
  refine ⟨q', ?_, hr⟩
  constructor
  intro i
  dsimp [q']
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  have : IsIso (q.generators i).π := hq.isIso i
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Invertible
