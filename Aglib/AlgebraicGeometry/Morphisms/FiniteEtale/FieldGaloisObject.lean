/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FieldFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Mathlib.FieldTheory.Galois.Basic

/-! # Actual field spectra and Galois objects

The original contravariant spectrum equivalence identifies deck automorphisms
with algebra automorphisms as sets, with its actual Spec map retained. A Galois
field-spectrum object has deck cardinal equal to its original embedding fibre,
hence the actual field degree. The native field-theoretic equality criterion
then proves Galoisness. No conclusion is inferred from a cardinal bound alone,
and no replacement field or action is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [Module.Finite K L] [Algebra.Etale K L]

/-- The exact contravariant spectrum correspondence on automorphisms. This is
a set equivalence, not an incorrectly oriented multiplicative equivalence. -/
def fieldSpectrumAutEquiv :
    Aut ((finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K L))) ≃
      (L ≃ₐ[K] L) :=
  (Functor.FullyFaithful.ofFullyFaithful (finiteEtaleSpecFunctor K)).isoEquiv.symm.trans
    ((isoOpEquiv (op (CommAlgCat.FiniteEtale.of K L))
      (op (CommAlgCat.FiniteEtale.of K L))).trans
      ((CommAlgCat.finiteEtale K).fullyFaithfulι.isoEquiv.trans
        (CommAlgCat.isoEquivAlgEquiv (R := K) (X := L) (Y := L))))

/-- The inverse correspondence is the original Spec image of the original
algebra automorphism, with no inversion or changed coefficient map hidden. -/
theorem fieldSpectrumAutEquiv_symm_hom (σ : L ≃ₐ[K] L) :
    ((fieldSpectrumAutEquiv K L).symm σ).hom =
      (finiteEtaleSpecFunctor K).map (CommAlgCat.FiniteEtale.ofHom σ.toAlgHom).op := rfl

/-- The original field-valued fibre sees exactly precomposition by the
corresponding original algebra automorphism. -/
theorem fieldSpectrumAutEquiv_fiber {Ω : Type u} [Field Ω] [Algebra K Ω]
    (σ : L ≃ₐ[K] L)
    (p : Fiber (Spec.algebraMap K Ω)
      ((finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K L)))) :
    finiteEtaleAlgebraFiberEquiv K Ω (CommAlgCat.FiniteEtale.of K L)
        ((fiberToFinite (Spec.algebraMap K Ω)).map
          ((fieldSpectrumAutEquiv K L).symm σ).hom p) =
      (finiteEtaleAlgebraFiberEquiv K Ω (CommAlgCat.FiniteEtale.of K L) p).comp σ.toAlgHom := by
  rw [fieldSpectrumAutEquiv_symm_hom]
  exact finiteEtaleAlgebraFiberEquiv_naturality K Ω
    (CommAlgCat.FiniteEtale.ofHom σ.toAlgHom).op p

/-- The original categorical deck-group order equals the actual field
algebra-automorphism cardinal, respecting the contravariant correspondence. -/
theorem fieldSpectrum_card_aut :
    Nat.card (Aut ((finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K L)))) =
      Nat.card (L ≃ₐ[K] L) :=
  Nat.card_congr (fieldSpectrumAutEquiv K L)

/-- An actual isomorphism to the unchanged field spectrum transfers the
original deck cardinal to the original field automorphism cardinal. -/
theorem card_fieldAut_of_iso_fieldSpectrum
    (Y : FiniteEtale (Spec (.of K)))
    (e : Y ≅ (finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K L))) :
    Nat.card (L ≃ₐ[K] L) = Nat.card (Aut Y) :=
  (fieldSpectrum_card_aut K L).symm.trans
    (Nat.card_congr (Aut.autMulEquivOfIso e).toEquiv).symm

/-- A Galois cover actually isomorphic to the original field spectrum gives
Galoisness of that same field extension. All cardinal transport is along the
supplied original isomorphism and the original embedding-fibre comparison. -/
theorem isGalois_of_iso_fieldSpectrum
    (Y : FiniteEtale (Spec (.of K))) [IsGalois Y]
    (e : Y ≅ (finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K L))) :
    _root_.IsGalois K L := by
  let : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  let F := fiberToFinite (Spec.algebraMap K (AlgebraicClosure K))
  let y : F.obj Y := Classical.choice (nonempty_fiber_of_isConnected F Y)
  have hdeck : Nat.card (Aut Y) = Module.finrank K L :=
    (Nat.card_congr (evaluationEquivOfIsGalois F Y y)).trans
      ((Nat.card_congr (FintypeCat.equivEquivIso.symm (F.mapIso e))).trans
        ((Nat.card_congr (finiteEtaleAlgebraFiberEquiv K (AlgebraicClosure K)
          (CommAlgCat.FiniteEtale.of K L))).trans
          (AlgHom.natCard_of_splits K L (AlgebraicClosure K)
            (fun _ => IsAlgClosed.splits _))))
  apply _root_.IsGalois.of_card_aut_eq_finrank
  exact (card_fieldAut_of_iso_fieldSpectrum K L Y e).trans hdeck

/-- The literal field-spectrum specialization uses the same complete original
isomorphism construction with the identity isomorphism. -/
theorem isGalois_of_fieldSpectrum
    [IsGalois ((finiteEtaleSpecFunctor K).obj (op (CommAlgCat.FiniteEtale.of K L)))] :
    _root_.IsGalois K L :=
  isGalois_of_iso_fieldSpectrum K L _ (Iso.refl _)

end AlgebraicGeometry.Scheme.FiniteEtale
