/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Complex
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.DeterminantSquare.Literal.OpenSquare

/-!
# The original determinant on an actual affine open square

The actual normal, middle and tangent arrows form the original conormal
complex map. The original arbitrary-section wedge formula gives equality
of its same whole determinant arrows. Raw normal, tangent, and middle
heads retain the literal original maps through the genuine degree cast.
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

private theorem determinantSquare_changeMaps
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    {C Q P : X.Modules} {C' Q' P' : X'.Modules}
    (Δ : tensorSheaf X C Q ≅ P) (Δ' : tensorSheaf X' C' Q' ≅ P')
    (aC : (restrictFunctor j).obj C ⟶ C')
    {aQ bQ : (restrictFunctor j).obj Q ⟶ Q'}
    {aP bP : (restrictFunctor j).obj P ⟶ P'}
    (hQ : aQ = bQ) (hP : aP = bP)
    (h : CanonicalDeterminantOpenSquare j C Q P C' Q' P' Δ Δ' aC aQ aP) :
    CanonicalDeterminantOpenSquare j C Q P C' Q' P' Δ Δ' aC bQ bP := by
  subst bQ bP
  exact h

/-- The original affine open determinant square with its literal quotient display data shared. -/
def CanonicalAmbientConormalDeterminantSquare
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
    (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : (α ≫ φ).hom.FormallySmooth)
    (hB' : ((α ≫ φ) ≫ regularListQuotientMap t).hom.FormallySmooth)
    {d : ℕ} (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing t)
      (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ regularListQuotientMap t)))
    (hc : t.length = s.length) : Prop :=
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap t
    let N := (pullback (Spec.map q)).obj (Hom.idealModule (Spec.map q))
    let N' := (pullback (Spec.map q')).obj (Hom.idealModule (Spec.map q'))
    let M := (pullback (Spec.map q)).obj (relativeDifferentialSheaf (Spec.map α))
    let M' := (pullback (Spec.map q')).obj (relativeDifferentialSheaf (Spec.map (α ≫ φ)))
    let Q := relativeDifferentialSheaf (Spec.map (α ≫ q))
    let Q' := relativeDifferentialSheaf (Spec.map ((α ≫ φ) ≫ q'))
    let Δ := regularListConormalDeterminantAt α (Ideal.ofList s) s.length d
      hA hB bQ s hs rfl rfl
    let Δ' := regularListConormalDeterminantAt (α ≫ φ) (Ideal.ofList t) s.length d
      hA' hB' bQ' t ht rfl hc
    CanonicalDeterminantOpenSquare (Spec.map ψ)
      (regularListNormalAt (Ideal.ofList s) s.length)
      (regularListTangentTopAt α (Ideal.ofList s) d)
      (regularListMiddleTopAt α (Ideal.ofList s) (s.length + d))
      (regularListNormalAt (Ideal.ofList t) s.length)
      (regularListTangentTopAt (α ≫ φ) (Ideal.ofList t) d)
      (regularListMiddleTopAt (α ≫ φ) (Ideal.ofList t) (s.length + d)) Δ Δ'
      (canonicalExteriorOpenMap (Spec.map ψ) N N' s.length
        (canonicalNormalOpenSquareMap (Spec.map q) (Spec.map q') (Spec.map φ) (Spec.map ψ)
          (canonicalAmbientClosedSquare φ q q' ψ h)))
      (canonicalExteriorOpenMap (Spec.map ψ) Q Q' d
        (canonicalAmbientConormalTangentIso α φ q q' ψ h).hom)
      (canonicalExteriorOpenMap (Spec.map ψ) M M' (s.length + d)
        (canonicalAmbientConormalMiddleIso α φ q q' ψ h).hom)

/-- The same original affine determinant square with the actual conormal-complex components. -/
def CanonicalAmbientConormalComplexDeterminantSquare
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
    (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : (α ≫ φ).hom.FormallySmooth)
    (hB' : ((α ≫ φ) ≫ regularListQuotientMap t).hom.FormallySmooth)
    {d : ℕ} (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing t)
      (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ regularListQuotientMap t)))
    (hc : t.length = s.length) : Prop :=
    let q := regularListQuotientMap s
    let q' := regularListQuotientMap t
    let N := (pullback (Spec.map q)).obj (Hom.idealModule (Spec.map q))
    let N' := (pullback (Spec.map q')).obj (Hom.idealModule (Spec.map q'))
    let M := (pullback (Spec.map q)).obj (relativeDifferentialSheaf (Spec.map α))
    let M' := (pullback (Spec.map q')).obj (relativeDifferentialSheaf (Spec.map (α ≫ φ)))
    let Q := relativeDifferentialSheaf (Spec.map (α ≫ q))
    let Q' := relativeDifferentialSheaf (Spec.map ((α ≫ φ) ≫ q'))
    let Δ := regularListConormalDeterminantAt α (Ideal.ofList s) s.length d
      hA hB bQ s hs rfl rfl
    let Δ' := regularListConormalDeterminantAt (α ≫ φ) (Ideal.ofList t) s.length d
      hA' hB' bQ' t ht rfl hc
    let Φ := canonicalAmbientConormalComplexMap α φ q q' ψ h
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
    CanonicalDeterminantOpenSquare (Spec.map ψ)
      (regularListNormalAt (Ideal.ofList s) s.length)
      (regularListTangentTopAt α (Ideal.ofList s) d)
      (regularListMiddleTopAt α (Ideal.ofList s) (s.length + d))
      (regularListNormalAt (Ideal.ofList t) s.length)
      (regularListTangentTopAt (α ≫ φ) (Ideal.ofList t) d)
      (regularListMiddleTopAt (α ≫ φ) (Ideal.ofList t) (s.length + d)) Δ Δ'
      (canonicalExteriorOpenMap (Spec.map ψ) N N' s.length
        (canonicalNormalOpenSquareMap (Spec.map q) (Spec.map q') (Spec.map φ) (Spec.map ψ)
          (canonicalAmbientClosedSquare φ q q' ψ h)))
      (canonicalExteriorOpenMap (Spec.map ψ) Q Q' d
        Φ.τ₃)
      (canonicalExteriorOpenMap (Spec.map ψ) M M' (s.length + d)
        Φ.τ₂)

/-- The original wedge laws and actual original normal column give the whole complex square. -/
theorem canonicalAmbientConormalDeterminant_complex
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
    (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : (α ≫ φ).hom.FormallySmooth)
    (hB' : ((α ≫ φ) ≫ regularListQuotientMap t).hom.FormallySmooth)
    {d : ℕ} (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing t)
      (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ regularListQuotientMap t)))
    (hc : t.length = s.length) :
    CanonicalAmbientConormalComplexDeterminantSquare α s t hs ht φ ψ h
      hA hB hA' hB' bQ bQ' hc := by
  exact canonicalConormalLiteralOpenSquare α (α ≫ φ) (Ideal.ofList s) (Ideal.ofList t)
    s.length d (Spec.map ψ) hA hB hA' hB' bQ bQ' s t hs ht rfl rfl rfl hc
    (canonicalNormalOpenSquareMap (Spec.map (regularListQuotientMap s))
      (Spec.map (regularListQuotientMap t)) (Spec.map φ) (Spec.map ψ)
      (canonicalAmbientClosedSquare φ (regularListQuotientMap s)
        (regularListQuotientMap t) ψ h))
    (canonicalAmbientConormalComplexMap α φ (regularListQuotientMap s)
      (regularListQuotientMap t) ψ h Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective)
    (canonicalAmbientConormalComplexMap_normal α φ (regularListQuotientMap s)
      (regularListQuotientMap t) ψ h Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective)

/-- The same original determinant commutes with the actual normal, middle and tangent arrows.
All objects are the literal quotients and the original determinant in the genuine common degree. -/
theorem canonicalAmbientConormalDeterminant
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
    (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
    (hA' : (α ≫ φ).hom.FormallySmooth)
    (hB' : ((α ≫ φ) ≫ regularListQuotientMap t).hom.FormallySmooth)
    {d : ℕ} (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
    (bQ' : Module.Basis (Fin d) (regularListQuotientRing t)
      (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ regularListQuotientMap t)))
    (hc : t.length = s.length) :
    CanonicalAmbientConormalDeterminantSquare α s t hs ht φ ψ h hA hB hA' hB' bQ bQ' hc := by
  let q := regularListQuotientMap s
  let q' := regularListQuotientMap t
  let N := (pullback (Spec.map q)).obj (Hom.idealModule (Spec.map q))
  let N' := (pullback (Spec.map q')).obj (Hom.idealModule (Spec.map q'))
  let M := (pullback (Spec.map q)).obj (relativeDifferentialSheaf (Spec.map α))
  let M' := (pullback (Spec.map q')).obj (relativeDifferentialSheaf (Spec.map (α ≫ φ)))
  let Q := relativeDifferentialSheaf (Spec.map (α ≫ q))
  let Q' := relativeDifferentialSheaf (Spec.map ((α ≫ φ) ≫ q'))
  let Δ := regularListConormalDeterminantAt α (Ideal.ofList s) s.length d
    hA hB bQ s hs rfl rfl
  let Δ' := regularListConormalDeterminantAt (α ≫ φ) (Ideal.ofList t) s.length d
    hA' hB' bQ' t ht rfl hc
  let j := Spec.map ψ
  let aN := canonicalNormalOpenSquareMap (Spec.map q) (Spec.map q') (Spec.map φ) j
    (canonicalAmbientClosedSquare φ q q' ψ h)
  have hQ := congrArg (fun f : (restrictFunctor j).obj Q ⟶ Q' =>
    canonicalExteriorOpenMap j Q Q' d f)
      (canonicalAmbientConormalComplexMap_tangent α φ q q' ψ h
        Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective)
  have hM := congrArg (fun f : (restrictFunctor j).obj M ⟶ M' =>
    canonicalExteriorOpenMap j M M' (s.length + d) f)
      (canonicalAmbientConormalComplexMap_middle α φ q q' ψ h
        Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective)
  exact determinantSquare_changeMaps j Δ Δ'
    (canonicalExteriorOpenMap j N N' s.length aN) hQ hM
    (canonicalAmbientConormalDeterminant_complex α s t hs ht φ ψ h hA hB hA' hB'
      bQ bQ' hc)

end AlgebraicGeometry.Scheme.Modules
