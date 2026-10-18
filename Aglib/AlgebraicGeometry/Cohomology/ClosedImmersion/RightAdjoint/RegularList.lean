/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Affine
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.RegularList
public import Aglib.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.AcyclicSingle
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Original derived sections for a regular affine closed immersion

Let `s` be a finite weakly regular list in a commutative ring `R`. For a
quasicoherent coefficient `L` on `Spec R`, a supplied original sections
isomorphism `Γ_R L ≅ R` identifies actual `RΓ_(R/(s)) (Ri! L)` with the
original quotient ring single in degree `s.length`.

The map uses the one native closed right adjoint, its original affine
comparison, the native acyclic-single comparison for affine sections,
the supplied coefficient trivialization and the original regular-list
coinduction calculation. All four derived sizes and the supported Ext
size remain independent. The result is independent of the supplied ring
injective resolution. No Noetherian, flatness, nontrivial-ring or
proper-ideal premise is imposed.

The conclusion is an isomorphism after actual derived sections. It does
not yet identify the sheaf Ri! with a shifted line: original localization,
full Koszul top-class and determinant comparisons remain separate gates.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules RingTheory.Sequence
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w a b v z
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} [HasExt.{w} (ModuleCat.{u} R)]
  (s : List R) (hs : IsWeaklyRegular R s)
  [HasDerivedCategory.{a} (Spec R).Modules]
  [HasDerivedCategory.{b} (Spec (.of (R ⧸ Ideal.ofList s))).Modules]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]
  [HasDerivedCategory.{z} (ModuleCat.{u} (R ⧸ Ideal.ofList s))]

/-- The actual derived sections of Ri! of a framed affine coefficient are the quotient single. -/
def derivedClosedImmersionRightAdjointRegularListSectionsIso
    (L : (Spec R).Modules) [L.IsQuasicoherent]
    (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)
    (J : InjectiveResolution (ModuleCat.of R R)) :
    letI := moduleSpecΓFunctor_additive (CommRingCat.of (R ⧸ Ideal.ofList s))
    (((closedImmersionRightAdjoint (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s))))).rightDerivedFunctorPlus ⋙
      (moduleSpecΓFunctor (R := .of (R ⧸ Ideal.ofList s))).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L)) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} (R ⧸ Ideal.ofList s))
        (s.length : ℤ)).obj (ModuleCat.of (R ⧸ Ideal.ofList s) (R ⧸ Ideal.ofList s)) := by
  letI := moduleSpecΓFunctor_additive (CommRingCat.of (R ⧸ Ideal.ofList s))
  let φ : R ⟶ CommRingCat.of (R ⧸ Ideal.ofList s) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s))
  let G := moduleSpecΓFunctor (R := R)
  let C := ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))
  letI : G.IsRightAdjoint := (tilde.adjunction (R := R)).isRightAdjoint
  let eΓ := G.rightDerivedFunctorPlusSingleIsoOfAcyclic L
    (AffineDerived.isZero_rightDerived_globalSections_succ L)
  exact (derivedClosedImmersionRightAdjointAffineIso φ).app
      ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj L) ≪≫
    C.rightDerivedFunctorPlus.mapIso (eΓ ≪≫
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).mapIso e) ≪≫
    ModuleCat.derivedCoextendScalarsPlusRegularListRingIso.{u,w,v,z} s hs J

/-- The ordered actual derived-sections comparison is independent of the supplied resolution. -/
theorem derivedClosedImmersionRightAdjointRegularListSectionsIso_independent
    (L : (Spec R).Modules) [L.IsQuasicoherent]
    (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)
    (I J : InjectiveResolution (ModuleCat.of R R)) :
    derivedClosedImmersionRightAdjointRegularListSectionsIso s hs L e I =
      derivedClosedImmersionRightAdjointRegularListSectionsIso s hs L e J := by
  unfold derivedClosedImmersionRightAdjointRegularListSectionsIso
  rw [ModuleCat.derivedCoextendScalarsPlusRegularListRingIso_independent s hs I J]

end AlgebraicGeometry.Scheme.Modules
