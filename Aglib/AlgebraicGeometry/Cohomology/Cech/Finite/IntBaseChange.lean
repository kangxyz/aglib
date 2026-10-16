/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Embedding.MapExtend
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Truncation
public import Aglib.AlgebraicGeometry.Cohomology.Cech.ModuleBaseChange

/-!
# The original Cech base-change map in integer degrees

The existing natural-number Cech base-change map extends through the native
zero-extension comparison. The retained-degree equation preserves the
original Cech arrow, its actual scalar transport and its original geometric
pullback unit. A finite affine family in a separated scheme makes the map
invertible for every ring homomorphism, without coefficient relative flatness
or a cover hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R B : Type u} [CommRing R] [CommRing B] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (σ : R →+* B) (M : X.Modules)
  {ι : Type u} [Finite ι] (U : ι → X.Opens)

/-- The original Cech scalar-extension map, transported through native
extension by zero from natural-number to integer degrees. -/
def moduleCechIntBaseChangeMap :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleCechIntComplex X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M) ⟶
      moduleCechIntComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
        (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
        (fun i => p ⁻¹ᵁ U i) ((Scheme.Modules.pullback p).obj M) :=
  ((moduleCechComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U).mapExtendIso
        (ModuleCat.extendScalars σ) ComplexShape.embeddingUpNat).hom ≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} B)).map
      (moduleCechBaseChangeMap f σ M U)

/-- Retained degrees have exactly the original Cech base-change component,
through the two original native zero-extension term transports. -/
@[reassoc]
theorem moduleCechIntBaseChangeMap_f_extendXIso (n : ℕ) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let C := moduleCechComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U
    let D := moduleCechComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      ((Scheme.Modules.pullback p).obj M) (fun i => p ⁻¹ᵁ U i)
    (moduleCechIntBaseChangeMap f σ M U).f (n : ℤ) ≫
        (D.extendXIso ComplexShape.embeddingUpNat rfl).hom =
      (ModuleCat.extendScalars σ).map
        (C.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
          (moduleCechBaseChangeMap f σ M U).f n := by
  dsimp only
  let C : CochainComplex (ModuleCat.{u} R) ℕ := moduleCechComplex X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M U
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let D : CochainComplex (ModuleCat.{u} B) ℕ :=
    moduleCechComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
    (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
    ((Scheme.Modules.pullback p).obj M) (fun i => p ⁻¹ᵁ U i)
  let θ : ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℕ)).obj C ⟶ D :=
    moduleCechBaseChangeMap f σ M U
  change ((C.mapExtendIso (ModuleCat.extendScalars σ) ComplexShape.embeddingUpNat).hom.f
      (n : ℤ) ≫ (HomologicalComplex.extendMap θ ComplexShape.embeddingUpNat).f (n : ℤ)) ≫
        (D.extendXIso ComplexShape.embeddingUpNat rfl).hom =
      (ModuleCat.extendScalars σ).map (C.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        θ.f n
  rw [HomologicalComplex.extendMap_f θ ComplexShape.embeddingUpNat
    (i := n) (i' := (n : ℤ)) rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, C.mapExtendIso_hom_f_extendXIso
    (ModuleCat.extendScalars σ) ComplexShape.embeddingUpNat (i := n) (j := (n : ℤ)) rfl]

/-- The original integer Cech map is invertible after every ring map for
a finite affine family in a separated scheme. No cover or flatness is needed. -/
theorem moduleCechIntBaseChangeMap_isIso [X.IsSeparated] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) : IsIso (moduleCechIntBaseChangeMap f σ M U) := by
  let := moduleCechBaseChangeMap_isIso f σ M U hU
  dsimp only [moduleCechIntBaseChangeMap]
  infer_instance

/-- The canonical isomorphism packages the same original integer Cech map. -/
def moduleCechIntBaseChangeIso [X.IsSeparated] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) :
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleCechIntComplex X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M) ≅
      moduleCechIntComplex (pullback f (Spec.map (CommRingCat.ofHom σ)))
        (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
        (fun i => p ⁻¹ᵁ U i) ((Scheme.Modules.pullback p).obj M) := by
  letI := moduleCechIntBaseChangeMap_isIso f σ M U hU
  exact asIso (moduleCechIntBaseChangeMap f σ M U)

/-- The packaged comparison keeps the literal original integer Cech arrow. -/
@[simp]
theorem moduleCechIntBaseChangeIso_hom [X.IsSeparated] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) :
    (moduleCechIntBaseChangeIso f σ M U hU).hom = moduleCechIntBaseChangeMap f σ M U := rfl

end AlgebraicGeometry.Scheme.Cohomology
