/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.RingTheory.Descent.PurelyInseparable.BaseChange
public import Aglib.RingTheory.Descent.Canonical

/-!
# Full faithfulness of affine finite purely inseparable scalar extension

Finite purely inseparable extension induces a bijection on algebra Hom sets
after arbitrary affine base change when the source algebra is étale. The target
algebra is arbitrary, and all maps are the actual tensor-product maps.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.GlobalFinitePureAlgebraMaps` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`727f0c2493ff24afa616b9d34f879c85507840716ef547472a3e5a13bece9fba`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section

open scoped _root_.TensorProduct

namespace Algebra.Descent.PurelyInseparable

open Algebra.Descent

universe u v w a b

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] [Module.Finite K L]
  (R : Type w) [CommRing R] [Algebra K R]
  (A : Type a) (B : Type b) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The scalar-extension map on algebra homomorphisms along R → R ⊗[K] L. -/
abbrev tensorMap (f : A →ₐ[R] B) :
    (R ⊗[K] L) ⊗[R] A →ₐ[R ⊗[K] L] (R ⊗[K] L) ⊗[R] B :=
  Algebra.TensorProduct.map (AlgHom.id (R ⊗[K] L) (R ⊗[K] L)) f

omit [IsPurelyInseparable K L] [Module.Finite K L] in
theorem tensorMap_injective : Function.Injective (tensorMap K L R A B) := by
  intro f g h
  ext x
  apply (canonicalInvariantsEquiv R (R ⊗[K] L) B).injective
  apply Subtype.ext
  exact AlgHom.congr_fun h (1 ⊗ₜ[R] x)

variable [Algebra.Etale R A]

/-- Any map after finite purely inseparable scalar extension respects the
canonical descent data, by uniqueness of lifting through the nilpotent counit. -/
def canonicalDatumHom
    (f : (R ⊗[K] L) ⊗[R] A →ₐ[R ⊗[K] L] (R ⊗[K] L) ⊗[R] B) :
    (canonicalDatum R (R ⊗[K] L) A).Hom (canonicalDatum R (R ⊗[K] L) B) where
  hom := f
  comm := by
    let S := R ⊗[K] L
    let μ := counit R S (S ⊗[R] B)
    have hmap : μ.comp (Algebra.TensorProduct.map (AlgHom.id S S)
        (f.restrictScalars R)) = f.comp (counit R S (S ⊗[R] A)) := by
      apply AlgHom.ext
      intro z
      induction z using _root_.TensorProduct.inductionOn with
      | tmul s x => exact (map_smul f s x).symm
      | add x y hx hy => simp only [map_add, hx, hy]
    apply (Algebra.FormallyEtale.formallyEtale_comp_bijective μ
      (Algebra.Descent.Nilpotent.counit_surjective R S _)
      (counit_baseChanged_ker_isNilpotent K L R (S ⊗[R] B))).injective
    change μ.comp ((canonicalDatum R S B).coaction.comp f) =
      μ.comp ((Algebra.TensorProduct.map (AlgHom.id S S) (f.restrictScalars R)).comp
        (canonicalDatum R S A).coaction)
    rw [← AlgHom.comp_assoc, (canonicalDatum R S B).counit_coaction, AlgHom.id_comp,
      ← AlgHom.comp_assoc, hmap, AlgHom.comp_assoc,
      (canonicalDatum R S A).counit_coaction, AlgHom.comp_id]

/-- The descended algebra map, obtained from the actual canonical equalizers. -/
def descendTensorMap
    (f : (R ⊗[K] L) ⊗[R] A →ₐ[R ⊗[K] L] (R ⊗[K] L) ⊗[R] B) : A →ₐ[R] B :=
  (canonicalInvariantsEquiv R (R ⊗[K] L) B).symm.toAlgHom.comp
    ((canonicalDatumHom K L R A B f).invariantsMap.comp
      (canonicalInvariantsEquiv R (R ⊗[K] L) A).toAlgHom)

theorem tensorMap_descendTensorMap
    (f : (R ⊗[K] L) ⊗[R] A →ₐ[R ⊗[K] L] (R ⊗[K] L) ⊗[R] B) :
    tensorMap K L R A B (descendTensorMap K L R A B f) = f := by
  ext x
  have h := (canonicalInvariantsEquiv R (R ⊗[K] L) B).apply_symm_apply
    ((canonicalDatumHom K L R A B f).invariantsMap
      (canonicalInvariantsEquiv R (R ⊗[K] L) A x))
  exact congrArg Subtype.val h

/-- Exact affine Hom-set invariance; the source algebra is étale and the target
is arbitrary. No Noetherian or finite type condition is imposed on `R`. -/
theorem tensorMap_bijective : Function.Bijective (tensorMap K L R A B) :=
  ⟨tensorMap_injective K L R A B,
    fun f ↦ ⟨descendTensorMap K L R A B f, tensorMap_descendTensorMap K L R A B f⟩⟩

end Algebra.Descent.PurelyInseparable
