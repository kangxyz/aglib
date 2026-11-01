/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Field comparison from the original invertible tensor map

The original tensor mate, its unit formula, faithful vanishing reflection and
field dimension comparison are constructed once. Invertibility is supplied by
geometric adapters; no quasicoherence or separation is hidden in this layer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X : Scheme.{u}} {k K : Type u} [Field k] [Field K]

/-- The original canonical cohomology tensor map is a linear equivalence after
an arbitrary field extension, provided that the original tensor map is invertible. -/
def moduleCohomologyFieldBaseChangeEquivOfIsIso
    (f : X ⟶ Spec (.of k))
    (σ : k →+* K) (M : X.Modules) (n : ℕ)
    [IsIso (moduleCohomologyBaseChangeMap f σ M n)] :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let N := (Scheme.Modules.pullback p).obj M
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI : Algebra k K := σ.toAlgebra
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom _ β N n
    K ⊗[k] Sheaf.H.{u + 1} (moduleAddSheaf X M) n ≃ₗ[K]
      Sheaf.H.{u + 1} (moduleAddSheaf _ N) n := by
  letI : Algebra k K := σ.toAlgebra
  letI := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) M n
  letI := moduleCohomologyModuleOfHom _
    ((pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom)
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) n
  exact (asIso (moduleCohomologyBaseChangeMap f σ M n)).toLinearEquiv

/-- The field-extension equivalence sends a unit pure tensor to the original
geometric coefficient pullback on cohomology. -/
theorem moduleCohomologyFieldBaseChangeEquivOfIsIso_one_tmul
    (f : X ⟶ Spec (.of k))
    (σ : k →+* K) (M : X.Modules) (n : ℕ)
    [IsIso (moduleCohomologyBaseChangeMap f σ M n)]
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    letI : Algebra k K := σ.toAlgebra
    letI := moduleCohomologyModuleOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) M n
    moduleCohomologyFieldBaseChangeEquivOfIsIso f σ M n ((1 : K) ⊗ₜ[k] x) =
      moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M n x := by
  exact moduleCohomologyBaseChangeMap_one_tmul f σ M n x

/-- Original module cohomology vanishes exactly when it vanishes after an
arbitrary extension of its structural field. No finiteness of cohomology is needed. -/
theorem subsingleton_moduleCohomology_iff_fieldBaseChange_of_isIso
    (f : X ⟶ Spec (.of k))
    (σ : k →+* K) (M : X.Modules) (n : ℕ)
    [IsIso (moduleCohomologyBaseChangeMap f σ M n)] :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) ↔
      Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf _ ((Scheme.Modules.pullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) n) := by
  let : Algebra k K := σ.toAlgebra
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) M n
  let e := moduleCohomologyFieldBaseChangeEquivOfIsIso f σ M n
  constructor
  · intro h
    let := h
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    exact congrArg e (Subsingleton.elim a b)
  · intro h
    let := h
    have hT : Subsingleton (K ⊗[k] Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :=
      ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k K).mp hT

/-- The dimensions over the original and extended structural fields agree,
through the same canonical cohomology comparison. -/
theorem moduleCohomology_finrank_fieldBaseChange_of_isIso
    (f : X ⟶ Spec (.of k))
    (σ : k →+* K) (M : X.Modules) (n : ℕ)
    [IsIso (moduleCohomologyBaseChangeMap f σ M n)] :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let N := (Scheme.Modules.pullback p).obj M
    letI := moduleCohomologyModuleOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) M n
    letI := moduleCohomologyModuleOfHom _
      (q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) N n
    Module.finrank K (Sheaf.H.{u + 1} (moduleAddSheaf _ N) n) =
      Module.finrank k (Sheaf.H.{u + 1} (moduleAddSheaf X M) n) := by
  let : Algebra k K := σ.toAlgebra
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) M n
  let := moduleCohomologyModuleOfHom _
    ((pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom)
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) n
  let e := moduleCohomologyFieldBaseChangeEquivOfIsIso f σ M n
  exact e.finrank_eq.symm.trans Module.finrank_baseChange

end AlgebraicGeometry.Scheme.Cohomology
