/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Truncation
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.AffineSections
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Flat original Cech section terms

Relative flatness of the actual quasicoherent coefficient supplies flatness
of the original structural-ring section presheaf on affine opens. Finite
products then make every original full-tuple Cech term flat, including the
unchanged integer extension. No cover, Noetherianity or finiteness of section
modules is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
  (hM : Scheme.Modules.relativeFlat f M)

include hM

/-- The existing structural-ring section presheaf is flat on every affine
open for an actual relatively flat quasicoherent coefficient. -/
theorem moduleSectionsPresheaf_flat_of_relativeFlat
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Flat R ((moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M).obj (op U)) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let ψ := (X.ringCatSheaf.obj.map
    ((isTerminalTop (α := X.Opens)).op.to (op U))).hom
  let β := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (by simp)).hom
  have hψ : ψ = (X.presheaf.map U.leTop.op).hom := by
    have ht : (isTerminalTop (α := X.Opens)).op.to (op U) = U.leTop.op :=
      Subsingleton.elim _ _
    dsimp only [ψ]
    rw [ht]
    rfl
  have he : β = ψ.comp α := by
    rw [hψ]
    rfl
  have H : Module.Flat R ((ModuleCat.restrictScalars β).obj (M.val.obj (op U))) :=
    Scheme.Modules.flat_affineOpen_sections_of_relativeFlat f M hM hU
  change Module.Flat R ((ModuleCat.restrictScalars α).obj
    ((ModuleCat.restrictScalars ψ).obj (M.val.obj (op U))))
  exact (Module.Flat.equiv_iff
    ((ModuleCat.restrictScalarsComp' α ψ β he).app (M.val.obj (op U))).symm.toLinearEquiv).mpr H

variable [X.IsSeparated] {ι : Type u} [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

include hU

/-- Every original full-tuple Cech term is flat over the original structural
ring. Finite affine families suffice; they need not cover the scheme. -/
theorem moduleCechComplex_flat_X_of_relativeFlat (n : ℕ) :
    Module.Flat R ((moduleCechComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U).X n) := by
  classical
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let T (a : Fin (n + 1) → ι) :=
    (moduleSectionsPresheaf X α M).obj (op (∏ᶜ fun k => U (a k)))
  have hT (a : Fin (n + 1) → ι) : Module.Flat R (T a) := by
    apply moduleSectionsPresheaf_flat_of_relativeFlat f M hM
    have he : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
      apply le_antisymm
      · exact le_iInf fun k => leOfHom (Limits.Pi.π _ k)
      · exact leOfHom (Limits.Pi.lift fun k => homOfLE (iInf_le _ k))
    rw [he]
    exact IsAffineOpen.iInf (fun k => hU (a k))
  let : Fintype (Fin (n + 1) → ι) := Fintype.ofFinite _
  have hD : Module.Flat R (Π₀ a, T a) := Module.Flat.dfinsupp_iff.mpr hT
  have hP : Module.Flat R (∀ a, T a) :=
    (Module.Flat.equiv_iff (DFinsupp.linearEquivFunOnFintype (R := R))).mp hD
  exact (Module.Flat.equiv_iff (ModuleCat.piIsoPi T).toLinearEquiv).mpr hP

/-- The unchanged integer extension of the original Cech complex has flat
terms as well; negative terms are the original zero objects. -/
theorem moduleCechIntComplex_flat_X_of_relativeFlat (q : ℤ) :
    Module.Flat R ((moduleCechIntComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M).X q) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  by_cases hq : 0 ≤ q
  · have H := moduleCechComplex_flat_X_of_relativeFlat f M hM U hU q.toNat
    exact (Module.Flat.equiv_iff
      ((moduleCechComplex X α M U).extendXIso ComplexShape.embeddingUpNat
        (Int.toNat_of_nonneg hq)).toLinearEquiv).mpr H
  · have hzero : IsZero ((moduleCechIntComplex X α U M).X q) :=
      (moduleCechComplex X α M U).isZero_extend_X ComplexShape.embeddingUpNat q (by
        intro i hi
        change (i : ℤ) = q at hi
        omega)
    let := ModuleCat.subsingleton_of_isZero hzero
    infer_instance

end AlgebraicGeometry.Scheme.Cohomology
