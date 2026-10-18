/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.DeterminantSquare

/-!
# The original wedge law with the native literal complex heads

The same native determinant is evaluated on its actual conormal-complex
sections. This source-only normalization is checked once before the
original geometric open square is instantiated.
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

/-- The original arbitrary-section determinant law on the actual native conormal complex. -/
def CanonicalConormalLiteralWedgeLaw
    {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ canonicalConormalQuotientMap I).hom.FormallySmooth)
    (bQ : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ canonicalConormalQuotientMap I)))
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) : Prop :=
  let B := CommRingCat.of (A ⧸ I)
  let q := canonicalConormalQuotientMap I
  let K := relativeConormalAffineComplex α q Ideal.Quotient.mk_surjective
  let eN := relativeConormalAffineIdealPullbackIso α q Ideal.Quotient.mk_surjective
  ∀ (U : (Spec B).Opens)
    (v : Fin c → (canonicalConormalNormalSheaf I).val.obj (op U))
    (w : Fin d → K.X₂.val.obj (op U)),
    (regularListConormalDeterminantAt α I c d hA hB bQ s hs hI hc).hom.val.app (op U)
      (moduleTensorSection (Spec B) (regularListNormalAt I c) (regularListTangentTopAt α I d) U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf
          (canonicalConormalNormalSheaf I) c).app (op U) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf K.X₃ d).app (op U)
          (fun i => K.g.val.app (op U) (w i)))) =
      (SheafOfModulesOfCommRing.exteriorPowerMk (Spec B).sheaf K.X₂ (c + d)).app (op U)
        (Fin.append (fun i => K.f.val.app (op U) (eN.hom.val.app (op U) (v i))) w)

/-- The native raw-head section formula has exactly the original literal-complex formulation. -/
theorem canonicalConormalLiteralWedgeLaw
    {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ canonicalConormalQuotientMap I).hom.FormallySmooth)
    (bQ : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ canonicalConormalQuotientMap I)))
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    CanonicalConormalLiteralWedgeLaw α I c d hA hB bQ s hs hI hc := by
  intro U v w
  exact canonicalConormalDeterminantAt_sectionWedge α I c d hA hB bQ s hs hI hc U v w

/-- The original conormal complex with its literal quotient presentation retained. -/
abbrev canonicalConormalLiteralComplex
    {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) :=
  relativeConormalAffineComplex α (canonicalConormalQuotientMap I) Ideal.Quotient.mk_surjective

/-- An actual original source test, with its native tuple carriers displayed once. -/
structure CanonicalConormalLiteralSourceTest
    {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) where
  /-- The original normal/tangent tensor unit frame. -/
  frame : tensorSheaf (Spec (CommRingCat.of (A ⧸ I)))
      (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ I)))
        (canonicalConormalNormalSheaf I) c)
      (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ I)))
        (canonicalConormalLiteralComplex α I).X₃ d) ≅
    SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf
  /-- Actual original normal sections. -/
  normal : Fin c → (canonicalConormalNormalSheaf I).val.obj (op U)
  /-- Actual original middle sections lifting the tangent basis. -/
  middle : Fin d → (canonicalConormalLiteralComplex α I).X₂.val.obj (op U)
  /-- The same normal-first tensor evaluates to one in this original unit frame. -/
  one : frame.hom.val.app (op U)
      (moduleTensorSection (Spec (CommRingCat.of (A ⧸ I)))
        (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ I)))
          (canonicalConormalNormalSheaf I) c)
        (moduleExteriorPower (Spec (CommRingCat.of (A ⧸ I)))
          (canonicalConormalLiteralComplex α I).X₃ d) U
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec (CommRingCat.of (A ⧸ I))).sheaf
          (canonicalConormalNormalSheaf I) c).app (op U) normal)
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec (CommRingCat.of (A ⧸ I))).sheaf
          (canonicalConormalLiteralComplex α I).X₃ d).app (op U)
          (fun i => (canonicalConormalLiteralComplex α I).g.val.app (op U) (middle i)))) =
    (1 : Γ(Spec (CommRingCat.of (A ⧸ I)), U))

/-- The native basis and original epimorphism produce this actual source test.
The displayed carriers retain the same original sheaf sections. -/
@[no_expose] def canonicalConormalLiteralSourceTest
    {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c)
    (bQ : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
      (CommRingCat.KaehlerDifferential (α ≫ canonicalConormalQuotientMap I)))
    (U : (Spec (CommRingCat.of (A ⧸ I))).Opens) :
    CanonicalConormalLiteralSourceTest α I c d U :=
  Classical.choice (by
    obtain ⟨eS, v, w, hz⟩ := canonicalConormalSourceWedgeFrame α I c d s hs hI hc bQ U
    exact ⟨⟨eS, v, w, hz⟩⟩)

end AlgebraicGeometry.Scheme.Modules
