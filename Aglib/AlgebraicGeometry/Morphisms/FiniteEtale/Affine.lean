/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLimits
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! The actual spectrum functor from finite-etale algebras to finite-etale
covers of a field spectrum. The algebra/scheme bridge has no Galois input. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u
variable (K : Type u) [Field K]

/-- The contravariant spectrum functor from commutative `K` -algebras to schemes over `Spec K`
. -/
def algebraSpecOver : (CommAlgCat.{u} K)ᵒᵖ ⥤ Over (Spec (CommRingCat.of K)) :=
  (commAlgCatEquivUnder (CommRingCat.of K)).op.functor ⋙
    (Over.opEquivOpUnder (CommRingCat.of K)).inverse ⋙
      Over.post Scheme.Spec

@[simp] theorem algebraSpecOver_obj_left (A : CommAlgCat.{u} K) :
    ((algebraSpecOver K).obj (op A)).left = Spec (CommRingCat.of A) := rfl

@[simp] theorem algebraSpecOver_obj_hom (A : CommAlgCat.{u} K) :
    ((algebraSpecOver K).obj (op A)).hom =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := rfl

@[simp] theorem algebraSpecOver_map_left {A B : CommAlgCat.{u} K} (f : A ⟶ B) :
    ((algebraSpecOver K).map f.op).left = Spec.map (CommRingCat.ofHom f.hom.toRingHom) := rfl

/-- Full faithfulness of the spectrum functor from opposite `K` -algebras to schemes over
`Spec K` . -/
def algebraSpecOverFullyFaithful : (algebraSpecOver K).FullyFaithful :=
  ((commAlgCatEquivUnder (CommRingCat.of K)).op.trans
    (Over.opEquivOpUnder (CommRingCat.of K)).symm).fullyFaithfulFunctor.comp
      (Spec.fullyFaithful.over _)

instance algebraSpecOver_full : (algebraSpecOver K).Full :=
  (algebraSpecOverFullyFaithful K).full

instance algebraSpecOver_faithful : (algebraSpecOver K).Faithful :=
  (algebraSpecOverFullyFaithful K).faithful

/-- The spectrum functor from opposite finite étale `K` -algebras to finite étale schemes over
`Spec K` . -/
def finiteEtaleSpecFunctor :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤ Scheme.FiniteEtale (Spec (CommRingCat.of K)) :=
  ObjectProperty.lift (_root_.AlgebraicGeometry.Scheme.finiteEtaleProperty
    (Spec (CommRingCat.of K)))
    ((CommAlgCat.finiteEtale K).ι.op ⋙ algebraSpecOver K) (fun A => by
      change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K A.unop))) ∧
        Etale (Spec.map (CommRingCat.ofHom (algebraMap K A.unop)))
      constructor
      · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
      · exact (HasRingHomProperty.Spec_iff (P := @Etale.{u})).mpr
          (RingHom.etale_algebraMap.mpr inferInstance))

instance finiteEtaleSpecFunctor_full : (finiteEtaleSpecFunctor K).Full := by
  dsimp only [finiteEtaleSpecFunctor]
  infer_instance

instance finiteEtaleSpecFunctor_faithful : (finiteEtaleSpecFunctor K).Faithful := by
  dsimp only [finiteEtaleSpecFunctor]
  infer_instance

/-- The global sections of `Y` , with the `K` -algebra structure induced by its map to
`Spec K` . -/
def overSpecGlobalSections (Y : Over (Spec (CommRingCat.of K))) : CommAlgCat.{u} K := by
  let a : K →+* Γ(Y.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.hom.appTop).hom
  let : Algebra K Γ(Y.left, ⊤) := a.toAlgebra
  exact CommAlgCat.of K Γ(Y.left, ⊤)

/-- The canonical isomorphism from the spectrum of global sections to an affine scheme over
`Spec K` . -/
def affineOverSpecIso (Y : Over (Spec (CommRingCat.of K))) [IsAffine Y.left] :
    (algebraSpecOver K).obj (op (overSpecGlobalSections K Y)) ≅ Y :=
  Over.isoMk Y.left.isoSpec.symm (by
    change Y.left.isoSpec.inv ≫ Y.hom =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.hom.appTop)
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp])

theorem overSpecGlobalSections_finiteEtale (Y : Scheme.FiniteEtale (Spec (CommRingCat.of K))) :
    CommAlgCat.finiteEtale K (overSpecGlobalSections K Y.obj) := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  let A := overSpecGlobalSections K Y.obj
  let e : (algebraSpecOver K).obj (op A) ≅ Y.obj := affineOverSpecIso K Y.obj
  have : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of K))).map e.hom))
  have hFinite : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    change IsFinite ((algebraSpecOver K).obj (op A)).hom
    rw [← Over.w e.hom]
    infer_instance
  have hEtale : Etale (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    change Etale ((algebraSpecOver K).obj (op A)).hom
    rw [← Over.w e.hom]
    infer_instance
  constructor
  · exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hFinite)
  · exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale.{u})).mp hEtale)

/-- The finite étale `K` -algebra of global sections of a finite étale scheme over `Spec K` . -/
def finiteEtaleAlgebraOfCover (Y : Scheme.FiniteEtale (Spec (CommRingCat.of K))) :
    CommAlgCat.FiniteEtale.{u} K :=
  ⟨overSpecGlobalSections K Y.obj, overSpecGlobalSections_finiteEtale K Y⟩

/-- The canonical isomorphism from the spectrum of the global sections algebra back to the
cover. -/
def finiteEtaleSpecCoverIso (Y : Scheme.FiniteEtale (Spec (CommRingCat.of K))) :
    (finiteEtaleSpecFunctor K).obj (op (finiteEtaleAlgebraOfCover K Y)) ≅ Y := by
  let : IsAffine Y.obj.left := isAffine_of_isAffineHom Y.obj.hom
  exact ObjectProperty.isoMk _ (affineOverSpecIso K Y.obj)

instance finiteEtaleSpecFunctor_essSurj : (finiteEtaleSpecFunctor K).EssSurj where
  mem_essImage Y := ⟨op (finiteEtaleAlgebraOfCover K Y), ⟨finiteEtaleSpecCoverIso K Y⟩⟩

instance finiteEtaleSpecFunctor_isEquivalence : (finiteEtaleSpecFunctor K).IsEquivalence where

/-- The spectrum equivalence between opposite finite étale `K` -algebras and finite étale
`Spec K` -schemes. -/
def finiteEtaleAlgebraSchemeEquivalence :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ Scheme.FiniteEtale (Spec (CommRingCat.of K)) :=
  (finiteEtaleSpecFunctor K).asEquivalence

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bbaa94a2a483fa3c7bbf0eedcd91632a3ca3bb22c92e9a91ab0cce59be38f8bf.
Definitions, hypotheses and universes are retained modulo native names. -/
