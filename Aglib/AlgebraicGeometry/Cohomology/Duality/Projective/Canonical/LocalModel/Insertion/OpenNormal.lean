/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Insertion.Degree
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Contraction.Insertion.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenTensor

/-!
# The original ordered normal insertion on an actual open square

The actual image law for the original ordered generators supplies the
original normal-frame square. The same determinant square then transports
the same original insertion in the genuine common normal degree.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual ordered-normal image law and same determinant square preserve the original
insertion, using the original target normal frame in the genuine common degree. -/
theorem regularListNormalInsertion_open
    {R A R' A' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (s : List A) (t : List A') (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A' t) (hc : t.length = s.length)
    (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (H : Spec.map ψ ≫ Spec.map (regularListQuotientMap s) =
      Spec.map (regularListQuotientMap t) ≫ Spec.map φ)
    (hst : ∀ i : Fin s.length,
      φ (s.get i) = t.get (Fin.cast hc.symm i))
    {Q P : (Spec (regularListQuotientRing s)).Modules}
    {Q' P' : (Spec (regularListQuotientRing t)).Modules}
    (Δ : tensorSheaf _ (closedImmersionRegularListNormalLineBundle α s hs).val Q ≅ P)
    (Δ' : tensorSheaf _ (regularListNormalLineInDegree α' t ht s.length hc).val Q' ≅ P')
    (aQ : Q.restrict (Spec.map ψ) ⟶ Q') (bP : P.restrict (Spec.map ψ) ⟶ P')
    (hΔ : (restrictFunctor (Spec.map ψ)).map Δ.hom ≫ bP =
      canonicalTensorOpenMap (Spec.map ψ)
        (closedImmersionRegularListNormalLineBundle α s hs).val Q
        (regularListNormalLineInDegree α' t ht s.length hc).val Q'
        (canonicalNormalTopOpenMap (regularListQuotientMap s) (regularListQuotientMap t)
          φ ψ H s.length) aQ ≫ Δ'.hom) :
    (restrictFunctor (Spec.map ψ)).map
        (normalDeterminantInsertionIso (closedImmersionRegularListNormalLineBundle α s hs)
          (closedImmersionRegularListNormalFrameIso α s hs) Δ).hom ≫ bP =
      aQ ≫ (normalDeterminantInsertionIso
        (regularListNormalLineInDegree α' t ht s.length hc)
        (canonicalAffineNormalFrameInDegree α' (regularListQuotientMap t)
          Ideal.Quotient.mk_surjective t ht Ideal.mk_ker.symm s.length hc) Δ').hom := by
  have hSource : canonicalAffineNormalFrameInDegree α (regularListQuotientMap s)
      Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm s.length rfl =
        closedImmersionRegularListNormalFrameIso α s hs := by
    have hTransport : (regularListNormalDegreeIso α s hs s.length rfl).symm ≪≫
        closedImmersionRegularListNormalFrameIso α s hs =
          closedImmersionRegularListNormalFrameIso α s hs := by
      apply Iso.ext
      change (𝟙 _) ≫ (closedImmersionRegularListNormalFrameIso α s hs).hom = _
      exact Category.id_comp _
    exact (regularListNormalFrameInDegree_eq α s hs s.length rfl).trans hTransport
  have hFrame := canonicalAffineNormalFrameInDegree_openSquare α α'
    (regularListQuotientMap s) (regularListQuotientMap t)
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective s t hs ht
    Ideal.mk_ker.symm Ideal.mk_ker.symm s.length rfl hc φ ψ H hst
  have hLeft := congrArg (fun f => (restrictFunctor (Spec.map ψ)).map f.hom ≫
    (restrictUnitIso (Spec.map ψ)).hom) hSource
  exact normalDeterminantInsertionIso_restrict (Spec.map ψ)
    (closedImmersionRegularListNormalLineBundle α s hs)
    (regularListNormalLineInDegree α' t ht s.length hc)
    (closedImmersionRegularListNormalFrameIso α s hs)
    (canonicalAffineNormalFrameInDegree α' (regularListQuotientMap t)
      Ideal.Quotient.mk_surjective t ht Ideal.mk_ker.symm s.length hc) Δ Δ'
    (canonicalNormalTopOpenMap (regularListQuotientMap s) (regularListQuotientMap t)
      φ ψ H s.length) aQ bP (hLeft.symm.trans hFrame) hΔ

end AlgebraicGeometry.Scheme.Modules
