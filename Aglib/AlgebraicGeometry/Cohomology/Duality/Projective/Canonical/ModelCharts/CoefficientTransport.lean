/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.CoefficientLine
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.GeneratorOverlap
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseModel

/-!
# The original common-ideal model arrow under actual coefficient isomorphisms

The actual resolution lift transports the original canonical arrow. Arbitrary
sections frames give the same arrow, so no frame-coherence premise is needed
for the direct and iterated restrictions of the fixed ambient resolution.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u w
namespace AlgebraicGeometry.Scheme.Modules

/-- Any actual coefficient isomorphism and its original resolution lift preserve the
original common-ideal canonical map, with arbitrary displayed sections frames. -/
theorem regularListCanonicalModelMapAt_coefficient
    {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c : ℕ)
    {L N : (Spec A).Modules} [L.IsQuasicoherent] [N.IsQuasicoherent]
    (J : InjectiveResolution L) (K : InjectiveResolution N)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
    (f : moduleSpecΓFunctor.obj N ≅ ModuleCat.of A A)
    [HasExt.{w} (ModuleCat.{u} A)]
    (E : L ≅ N) (φ : InjectiveResolution.Hom J K E.hom)
    {Q : (Spec (CommRingCat.of (A ⧸ I))).Modules}
    (Δ : tensorSheaf _ (regularListNormalAt I c) Q ≅
      (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))).obj L)
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    HomologicalComplex.homologyMap
      (((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))).mapHomologicalComplex (.up ℤ)).map φ.hom') (c : ℤ) ≫
      regularListCanonicalModelMapAt α I c K f
        (Δ ≪≫ (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
          A ⟶ CommRingCat.of (A ⧸ I)))).mapIso E) s hs hI hc =
    regularListCanonicalModelMapAt α I c J e Δ s hs hI hc := by
  subst I c
  let g := (moduleSpecΓFunctor.mapIso E).symm ≪≫ e
  have hg : e.inv ≫ moduleSpecΓFunctor.map E.hom = g.inv := by rfl
  have h := regularListCanonicalModelTopHomologyIso_coefficient s e g α hs E φ hg Δ
  have hf := regularListCanonicalModelTopHomologyIso_coefficient_independent α s hs g f K
    (Δ ≪≫ (pullback (Spec.map (regularListQuotientMap s))).mapIso E)
  have hF := congrArg
    (fun t => HomologicalComplex.homologyMap
      (((closedImmersionRightAdjoint (Spec.map (regularListQuotientMap s))).mapHomologicalComplex
        (.up ℤ)).map φ.hom') (s.length : ℤ) ≫ t) hf
  exact hF.symm.trans h

end AlgebraicGeometry.Scheme.Modules
