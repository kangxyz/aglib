/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.GeneratorOverlap

/-!
# Original fixed-model arrows under generator change

The same original installed-resolution unit identifies native top
homology with the ordinary homology of the supplied fixed resolution.
Canceling that same unit transports the original Koszul determinant
cancellation to equality of the actual ordinary canonical model arrows.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u w
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance modelOverlapStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- The actual ordinary model homology on the fixed quotient, resolution and degree. -/
abbrev regularListModelTopHomologyAt {A : CommRingCat.{u}} (I : Ideal A)
    {L : (Spec A).Modules} (J : InjectiveResolution L) (c : ℕ) :=
  (((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
    A ⟶ CommRingCat.of (A ⧸ I)))).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex).homology (c : ℤ)

private def originalModelIsoAt {A : CommRingCat.{u}} (I : Ideal A)
    {L : (Spec A).Modules} (J : InjectiveResolution L) (c : ℕ) :
    regularListNativeTopHomologyAt (L := L) I c ≅ regularListModelTopHomologyAt I J c :=
  (DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of (A ⧸ I))).Modules
    (c : ℤ)).mapIso
      (J.rightDerivedFunctorPlusIso (closedImmersionRightAdjoint
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
          A ⟶ CommRingCat.of (A ⧸ I))))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors
      (A := (Spec (CommRingCat.of (A ⧸ I))).Modules) (c : ℤ)).app
      ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
        A ⟶ CommRingCat.of (A ⧸ I)))).mapCochainComplexPlus.obj J.cochainComplexPlus)

section CommonModel
variable {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c : ℕ)
  {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]
  {Q : (Spec (CommRingCat.of (A ⧸ I))).Modules}
  (Δ : tensorSheaf (Spec (CommRingCat.of (A ⧸ I))) (regularListNormalAt I c) Q ≅
    (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      A ⟶ CommRingCat.of (A ⧸ I)))).obj L)

/-- The original ordinary canonical arrow, transported only by the genuine ideal and degree. -/
def regularListCanonicalModelMapAt (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    regularListModelTopHomologyAt I J c ⟶ Q := by
  subst I c
  exact (regularListCanonicalModelTopHomologyIso s hs e α J Δ).hom

private theorem originalModelIsoAt_presentation (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (hI : Ideal.ofList s = I) (hc : s.length = c) :
    (originalModelIsoAt I J c).hom ≫ regularListCanonicalModelMapAt α I c J e Δ s hs hI hc =
      regularListCanonicalMapAt α I c e Δ s hs hI hc := by
  subst I c
  have h := congrArg Iso.hom
    (regularListCanonicalModelTopHomologyIso_native s hs e α J Δ)
  rw [Iso.trans_hom, derivedClosedImmersionRightAdjointRegularListModelHomologyIso_hom] at h
  exact h

variable (f : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)

/-- The actual fixed-model canonical arrows agree for different generators and frames.
The same native model comparison cancels; no determinant-unit hypothesis is used. -/
theorem regularListCanonicalModelMapAt_generatorChange (s t : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) :
    regularListCanonicalModelMapAt α I c J e Δ s hs hsI hsc =
      regularListCanonicalModelMapAt α I c J f Δ t ht htI htc := by
  apply (cancel_epi (originalModelIsoAt I J c).hom).mp
  exact (originalModelIsoAt_presentation α I c J e Δ s hs hsI hsc).trans
    ((regularListCanonicalMapAt_coefficient_independent I e f c α Δ s hs hsI hsc).trans
      ((regularListCanonicalMapAt_generatorChange α I c f Δ s t hs ht hsI htI hsc htc M hM).trans
        (originalModelIsoAt_presentation α I c J f Δ t ht htI htc).symm))

end CommonModel

section ActualDeterminants
variable {R A : CommRingCat.{u}} (α : R ⟶ A) (I : Ideal A) (c d : ℕ)
  (hA : α.hom.FormallySmooth)
  (hB : (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
    A ⟶ CommRingCat.of (A ⧸ I))).hom.FormallySmooth)
  (bA bA' : Module.Basis (Fin (c + d)) A (CommRingCat.KaehlerDifferential α))
  (bQ bQ' : Module.Basis (Fin d) (CommRingCat.of (A ⧸ I))
    (CommRingCat.KaehlerDifferential (α ≫ (CommRingCat.ofHom (Ideal.Quotient.mk I) :
      A ⟶ CommRingCat.of (A ⧸ I)))))
  {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e f : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)]
  (E : L ≅ moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) (c + d))

/-- Actual canonical determinants and all displayed frames give equal original fixed-model
arrows on the common ideal and degree. -/
theorem affineRegularListCanonicalModelMapAt_overlap (s t : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    (ht : RingTheory.Sequence.IsWeaklyRegular A t)
    (hsI : Ideal.ofList s = I) (htI : Ideal.ofList t = I)
    (hsc : s.length = c) (htc : t.length = c)
    (M : Matrix (Fin s.length) (Fin s.length) A)
    (hM : t = List.ofFn (fun i => ∑ j, M i j * s.get j)) :
    regularListCanonicalModelMapAt α I c J e
      (regularListCanonicalDeterminantAt α I c d hA hB bA bQ s hs hsI hsc ≪≫
        (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
          A ⟶ CommRingCat.of (A ⧸ I)))).mapIso E.symm) s hs hsI hsc =
      regularListCanonicalModelMapAt α I c J f
        (regularListCanonicalDeterminantAt α I c d hA hB bA' bQ' t ht htI htc ≪≫
          (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) :
            A ⟶ CommRingCat.of (A ⧸ I)))).mapIso E.symm) t ht htI htc := by
  rw [regularListCanonicalDeterminantAt_allFrames α I c d hA hB bA bA' bQ bQ'
    s t hs ht hsI htI hsc htc]
  exact regularListCanonicalModelMapAt_generatorChange α I c J e _ f
    s t hs ht hsI htI hsc htc M hM

end ActualDeterminants
end AlgebraicGeometry.Scheme.Modules
