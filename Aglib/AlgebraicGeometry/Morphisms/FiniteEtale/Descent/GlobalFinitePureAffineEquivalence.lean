/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureAffine
public import Aglib.RingTheory.Descent.Basic
public import Aglib.RingTheory.Descent.Canonical
public import Aglib.RingTheory.Descent.Morphisms
public import Aglib.RingTheory.Descent.Nilpotent
public import Aglib.RingTheory.Descent.PurelyInseparable.BaseChange
public import Aglib.RingTheory.Descent.PurelyInseparable.Morphisms
public import Aglib.RingTheory.TensorProduct.PurelyInseparable

/-!
# GlobalFinitePureAffineEquivalence

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

open _root_.Algebra.Descent.PurelyInseparable (tensorMap tensorMap_bijective)

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
open AlgebraicGeometry.Scheme.FiniteEtale.AffineDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] [Module.Finite K L]
  (R : Type u) [CommRing R] [Algebra K R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem specCover_map_surjective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Algebra.Etale R A] [Module.Finite R B] [Algebra.Etale R B] :
    Function.Surjective ((baseChange (Spec.algebraMap R (R ⊗[K] L))).map :
      (specCover R B ⟶ specCover R A) → _) := by
  intro q
  let S := R ⊗[K] L
  let eA := specBaseChangeIso R S A
  let eB := specBaseChangeIso R S B
  let q' : specCover S (S ⊗[R] B) ⟶ specCover S (S ⊗[R] A) := eB.inv ≫ q ≫ eA.hom
  let φ : S ⊗[R] A →ₐ[S] S ⊗[R] B :=
    ((algSpec.fullyFaithful (R := CommRingCat.of S)).preimage
      (X := op (CommAlgCat.of S (S ⊗[R] B)))
      (Y := op (CommAlgCat.of S (S ⊗[R] A))) q'.hom).unop.hom
  have hφ : specCoverHom S (S ⊗[R] A) (S ⊗[R] B) φ = q' := by
    apply ObjectProperty.hom_ext
    exact (algSpec.fullyFaithful (R := CommRingCat.of S)).map_preimage
      (X := op (CommAlgCat.of S (S ⊗[R] B)))
      (Y := op (CommAlgCat.of S (S ⊗[R] A))) q'.hom
  obtain ⟨f, hf⟩ := (tensorMap_bijective K L R A B).surjective φ
  refine ⟨specCoverHom R A B f, ?_⟩
  apply (cancel_mono eA.hom).mp
  rw [specBaseChangeIso_naturality]
  change eB.hom ≫ specCoverHom S (S ⊗[R] A) (S ⊗[R] B) (tensorMap K L R A B f) =
    q ≫ eA.hom
  rw [hf, hφ]
  simp [q']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem affinePure_full : (baseChange (Spec.algebraMap R (R ⊗[K] L))).Full where
  map_surjective {Y Z} f := by
    let F := baseChange (Spec.algebraMap R (R ⊗[K] L))
    let M := algebraModel Y
    let N := algebraModel Z
    let g : F.obj (specCover R M.algebra) ⟶ F.obj (specCover R N.algebra) :=
      F.map M.coverIso.hom ≫ f ≫ F.map N.coverIso.inv
    obtain ⟨h, hh⟩ := specCover_map_surjective K L R N.algebra M.algebra g
    refine ⟨M.coverIso.inv ≫ h ≫ N.coverIso.hom, ?_⟩
    change F.map (M.coverIso.inv ≫ h ≫ N.coverIso.hom) = f
    rw [Functor.map_comp, Functor.map_comp]
    rw [hh]
    simp only [g, Category.assoc, Iso.map_inv_hom_id_assoc, Iso.map_inv_hom_id]
    exact Category.comp_id f

omit [Module.Finite K L] in
theorem affinePure_faithful : (baseChange (Spec.algebraMap R (R ⊗[K] L))).Faithful := by
  have hff : (algebraMap R (R ⊗[K] L)).FaithfullyFlat := by
    exact (RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance
  have hs := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R (R ⊗[K] L)))).mpr hff
  let : Flat (Spec.algebraMap R (R ⊗[K] L)) := hs.1
  let : Surjective (Spec.algebraMap R (R ⊗[K] L)) := hs.2
  exact baseChange_faithful_of_flat_surjective _

/-- Finite purely inseparable invariance for an arbitrary affine base, with
forward functor definitionally the repository's actual base-change functor. -/
def affinePureEquivalence :
    Scheme.FiniteEtale (Spec (CommRingCat.of R)) ≌ Scheme.FiniteEtale
      (Spec (CommRingCat.of (R ⊗[K] L))) := by
  let F := baseChange (Spec.algebraMap R (R ⊗[K] L))
  let : F.Full := affinePure_full K L R
  let : F.Faithful := affinePure_faithful K L R
  let : F.EssSurj := ⟨fun Y ↦ ⟨(affinePureCoverDescent K L R Y).1,
    ⟨(affinePureCoverDescent K L R Y).2⟩⟩⟩
  let : F.IsEquivalence := { }
  exact F.asEquivalence

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 feb3665729c8c079366bf22893ccc02e69b66aac7c14a1e22ab63fdfc2c52f10.
Definitions, hypotheses and universes are retained modulo native names. -/
