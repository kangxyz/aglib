/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.DeterminantSquare.Literal

/-!
# The original literal conormal wedge square

The original two wedge laws give the determinant square on literal quotient
heads. The normal column and complex map remain arbitrary here, so the
geometric producer can supply its original arrows without unfolding them.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The literal determinant square retains the actual native complex columns. -/
def CanonicalConormalLiteralOpenSquare
    {R A R' A' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (I : Ideal A) (I' : Ideal A') (c d : ℕ)
    (j : Spec (CommRingCat.of (A' ⧸ I')) ⟶ Spec (CommRingCat.of (A ⧸ I)))
    [IsOpenImmersion j]
    (Δ : tensorSheaf _ (regularListNormalAt I c) (regularListTangentTopAt α I d) ≅
      regularListMiddleTopAt α I (c + d))
    (Δ' : tensorSheaf _ (regularListNormalAt I' c) (regularListTangentTopAt α' I' d) ≅
      regularListMiddleTopAt α' I' (c + d))
    (aN : (restrictFunctor j).obj (canonicalConormalNormalSheaf I) ⟶
      canonicalConormalNormalSheaf I')
    (Φ : (canonicalConormalLiteralComplex α I).map (restrictFunctor j) ⟶
      canonicalConormalLiteralComplex α' I') : Prop :=
  CanonicalDeterminantOpenSquare j
    (regularListNormalAt I c) (regularListTangentTopAt α I d)
    (regularListMiddleTopAt α I (c + d))
    (regularListNormalAt I' c) (regularListTangentTopAt α' I' d)
    (regularListMiddleTopAt α' I' (c + d)) Δ Δ'
    (canonicalExteriorOpenMap j (canonicalConormalNormalSheaf I)
      (canonicalConormalNormalSheaf I') c aN)
    (canonicalExteriorOpenMap j
      (canonicalConormalLiteralComplex α I).X₃
      (canonicalConormalLiteralComplex α' I').X₃ d Φ.τ₃)
    (canonicalExteriorOpenMap j
      (canonicalConormalLiteralComplex α I).X₂
      (canonicalConormalLiteralComplex α' I').X₂ (c + d) Φ.τ₂)

/-- The native wedge laws and produced source frame prove the same literal whole square. -/
theorem canonicalConormalLiteralOpenSquare
    {R A R' A' : CommRingCat.{u}} (α : R ⟶ A) (α' : R' ⟶ A')
    (I : Ideal A) (I' : Ideal A') (c d : ℕ)
    (j : Spec (CommRingCat.of (A' ⧸ I')) ⟶ Spec (CommRingCat.of (A ⧸ I)))
    [IsOpenImmersion j]
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ canonicalConormalQuotientMap I).hom.FormallySmooth)
    (hA' : α'.hom.FormallySmooth)
    (hB' : (α' ≫ canonicalConormalQuotientMap I').hom.FormallySmooth)
    (bQ : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ canonicalConormalQuotientMap I)))
    (bQ' : Module.Basis (Fin d) (CommRingCat.of (A' ⧸ I'))
      (CommRingCat.KaehlerDifferential (α' ≫ canonicalConormalQuotientMap I')))
    (s : List A) (t : List A') (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
    (hI : Ideal.ofList s = I) (hI' : Ideal.ofList t = I')
    (hc : s.length = c) (hc' : t.length = c)
    (aN : (restrictFunctor j).obj (canonicalConormalNormalSheaf I) ⟶
      canonicalConormalNormalSheaf I')
    (Φ : (canonicalConormalLiteralComplex α I).map (restrictFunctor j) ⟶
      canonicalConormalLiteralComplex α' I')
    (hN : (restrictFunctor j).map
        (relativeConormalAffineIdealPullbackIso α (canonicalConormalQuotientMap I)
          Ideal.Quotient.mk_surjective).hom ≫ Φ.τ₁ =
      aN ≫ (relativeConormalAffineIdealPullbackIso α' (canonicalConormalQuotientMap I')
        Ideal.Quotient.mk_surjective).hom) :
    CanonicalConormalLiteralOpenSquare α α' I I' c d j
      (regularListConormalDeterminantAt α I c d hA hB bQ s hs hI hc)
      (regularListConormalDeterminantAt α' I' c d hA' hB' bQ' t ht hI' hc') aN Φ := by
  let T := canonicalConormalLiteralSourceTest α I c d s hs hI hc bQ (j ''ᵁ ⊤)
  exact canonicalDeterminantOpenSquare_of_wedgeFrame j
    (canonicalConormalNormalSheaf I) (canonicalConormalNormalSheaf I')
    (canonicalConormalLiteralComplex α I) (canonicalConormalLiteralComplex α' I')
    (relativeConormalAffineIdealPullbackIso α (canonicalConormalQuotientMap I)
      Ideal.Quotient.mk_surjective)
    (relativeConormalAffineIdealPullbackIso α' (canonicalConormalQuotientMap I')
      Ideal.Quotient.mk_surjective) c d
    (regularListConormalDeterminantAt α I c d hA hB bQ s hs hI hc)
    (regularListConormalDeterminantAt α' I' c d hA' hB' bQ' t ht hI' hc') aN Φ hN
    (canonicalConormalLiteralWedgeLaw α I c d hA hB bQ s hs hI hc)
    (canonicalConormalLiteralWedgeLaw α' I' c d hA' hB' bQ' t ht hI' hc')
    T.frame T.normal T.middle T.one

end AlgebraicGeometry.Scheme.Modules
