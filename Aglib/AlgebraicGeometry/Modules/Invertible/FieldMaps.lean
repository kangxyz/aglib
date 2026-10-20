/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.FunctionField
public import Aglib.AlgebraicGeometry.Modules.Invertible.Field

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.Field` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3a085beaba4f22fe3e70487dde08340b1826dc7e89f72e5f5ec678accbfd15c1`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (LineBundle)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual line bundles and nonzero maps over a field spectrum

A genuine local unit chart covers Spec K and gives an actual global unit
trivialization. An endomorphism of the structure module is multiplication by
its value on the global section 1; if nonzero, that scalar is a unit in the
actual global field. This proves every component is bijective. Conjugating
by the actual unit trivializations proves every nonzero map of line bundles
on Spec K invertible. No cohomology, Abel, C3 or retained theorem family is
used. These are the original proved B helpers extracted to their proper
generic layer; the old Abel declarations are preserved as wrappers.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable (K : Type u) [Field K]
theorem fieldUnitMap_isIso_of_ne_zero
    (φ : (show (Spec (.of K)).Modules from SheafOfModules.unit (Spec (.of K)).ringCatSheaf) ⟶
      (show (Spec (.of K)).Modules from SheafOfModules.unit (Spec (.of K)).ringCatSheaf))
    (hφ : φ ≠ 0) : IsIso φ := by
  let X := Spec (.of K)
  let c : Γ(X,⊤) := φ.val.app (op ⊤) (1 : Γ(X,⊤))
  have hscalar (U : X.Opens) (a : Γ(X,U)) :
      φ.val.app (op U) a = X.presheaf.map U.leTop.op c * a := by
    have hn := PresheafOfModules.naturality_apply φ.val U.leTop.op (1 : Γ(X,⊤))
    let ψ : Γ(X,U) →ₗ[Γ(X,U)] Γ(X,U) := (φ.val.app (op U)).hom
    have hl := ψ.map_smul a (1 : Γ(X,U))
    change ψ (a * 1) = a * ψ 1 at hl
    change ψ a = _
    rw [mul_one] at hl
    change ψ (X.presheaf.map U.leTop.op 1) = X.presheaf.map U.leTop.op c at hn
    rw [map_one] at hn
    rw [hl, hn, mul_comm]
  have hc : c ≠ 0 := by
    intro h
    apply hφ
    apply Scheme.Modules.hom_ext
    intro U
    ext a
    change φ.val.app (op U) a = 0
    rw [hscalar, h, map_zero, zero_mul]
  letI : Field Γ(X,⊤) := (isField_of_isIntegral_of_subsingleton X).toField
  have hu : IsUnit c := isUnit_iff_ne_zero.mpr hc
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun a : Γ(X,U) ↦ φ.val.app (op U) a)
  simp_rw [hscalar]
  exact IsUnit.isUnit_iff_mulLeft_bijective.mp (hu.map (X.presheaf.map U.leTop.op).hom)

theorem fieldLineBundleMap_isIso_of_ne_zero (L M : LineBundle (Spec (.of K)))
    (φ : (show (Spec (.of K)).Modules from L.val) ⟶ (show (Spec (.of K)).Modules from M.val))
    (hφ : φ ≠ 0) : IsIso φ := by
  obtain ⟨eL⟩ := fieldLineBundle_trivial K L
  obtain ⟨eM⟩ := fieldLineBundle_trivial K M
  have hn : eL.inv ≫ φ ≫ eM.hom ≠ 0 := by
    intro h
    apply hφ
    apply (cancel_epi eL.inv).mp
    apply (cancel_mono eM.hom).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using h
  haveI := fieldUnitMap_isIso_of_ne_zero K (eL.inv ≫ φ ≫ eM.hom) hn
  haveI := IsIso.of_isIso_comp_left eL.inv (φ ≫ eM.hom)
  exact IsIso.of_isIso_comp_right φ eM.hom
end AlgebraicGeometry.Scheme.Modules.Invertible
