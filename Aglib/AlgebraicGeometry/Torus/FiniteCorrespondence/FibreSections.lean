/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.Subscheme
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.PrincipalFibres

/-!
# FibreSections for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `FibreSections.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`358965d1216d8cb2b6b3e5ac2c9ab6c5549a0d67363432edde9171872c56e462`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Torus.FiniteCorrespondence.Fibre
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open LaurentSupport Subscheme CategoryTheory AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual affine coordinate ring of the closed subscheme, before choosing
or extracting any prime/quotient presentation. -/
abbrev Sections (I : (torusScheme R).IdealSheafData) : Type u := Γ(I.subscheme, ⊤)

/-- The Laurent algebra action on global sections induced by the closed subscheme inclusion. -/
instance sectionsAlgebra (I : (torusScheme R).IdealSheafData) :
    Algebra (Laurent R) (Sections I) :=
  (coordinateMap I.subschemeι).hom.toAlgebra

/-- The Laurent algebra map to global sections of the closed subscheme defined by `I`. -/
def sectionsMap (I : (torusScheme R).IdealSheafData) :
    Laurent R →ₐ[Laurent R] Sections I where
  __ := (coordinateMap I.subschemeι).hom
  commutes' _ := rfl

theorem sectionsMap_surjective (I : (torusScheme R).IdealSheafData) :
    Function.Surjective (sectionsMap I) :=
  (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top _⟩).comp
    (Scheme.ΓSpecIso (.of (Laurent R))).commRingCatIsoToRingEquiv.symm.surjective

/-- The presentation is proved by the actual surjective coordinate map. -/
def sectionsEquiv (I : (torusScheme R).IdealSheafData) :
    (Laurent R ⧸ definingIdeal I) ≃ₐ[Laurent R] Sections I :=
  Ideal.quotientKerAlgEquivOfSurjective (f := sectionsMap I) (sectionsMap_surjective I)

/-- Pullback of the ideal sheaf along the actual affine torus morphism. -/
def fibreIdeal (I : (torusScheme R).IdealSheafData) (f : Laurent R →+* Laurent S) :
    (torusScheme S).IdealSheafData :=
  I.comap (Spec.map (CommRingCat.ofHom f))

/-- The geometric object is canonically the categorical scheme fibre product. -/
def fibreIso (I : (torusScheme R).IdealSheafData) (f : Laurent R →+* Laurent S) :
    (fibreIdeal I f).subscheme ≅
      CategoryTheory.Limits.pullback (Spec.map (CommRingCat.ofHom f)) I.subschemeι :=
  I.comapIso _

/-- The actual fibre's section algebra is the literal quotient by the extended
ideal. This remains valid for nonreduced and nonflat scheme fibres. -/
def fibreSectionsEquiv (I : (torusScheme R).IdealSheafData)
    (f : Laurent R →+* Laurent S) :
    (Laurent S ⧸ (definingIdeal I).map f) ≃ₐ[Laurent S] Sections (fibreIdeal I f) :=
  (Ideal.quotientEquivAlgOfEq (Laurent S) (definingIdeal_comap I f).symm).trans
    (sectionsEquiv (fibreIdeal I f))

/-- Local coefficient of the actual scheme fibre, computed from its own
global-section algebra with the ambient torus action. Infinity is allowed here. -/
def geometricFibreLength (I : (torusScheme R).IdealSheafData)
    (f : Laurent R →+* Laurent S) (q : Ideal (Laurent S)) [q.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime q)
    (Localization.AtPrime q ⊗[Laurent S] Sections (fibreIdeal I f))

/-- This is an equality of actual module lengths, proved by base change of the
coordinate algebra equivalence, not an equality introduced into a record. -/
theorem geometricFibreLength_eq (I : (torusScheme R).IdealSheafData)
    (f : Laurent R →+* Laurent S) (q : Ideal (Laurent S)) [q.IsPrime] :
    geometricFibreLength I f q =
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⊗[Laurent S] (Laurent S ⧸ (definingIdeal I).map f)) :=
  ((fibreSectionsEquiv I f).toLinearEquiv.baseChange
    (Laurent S) (Localization.AtPrime q) _ _).length_eq.symm

section ScalarMap
variable [Algebra R S]

/-- For an independently specified actual integral torus subscheme, extraction
of its prime label preserves the actual geometric fibre coefficient. -/
theorem geometricFibreLength_toPoint [_root_.IsReduced R] (Z : FiniteDominantSubscheme R)
    (q : FiniteDominantPrime S) :
    geometricFibreLength Z.val (coefficientMap (algebraMap R S)) q.val =
      quotientFibreLength (S := S) (toPoint Z) q := by
  rw [geometricFibreLength_eq]
  rfl

/-- The same dictionary on the maintained prime-labelled generators. -/
theorem geometricFibreLength_ofPoint (p : FiniteDominantPrime R) (q : FiniteDominantPrime S) :
    geometricFibreLength (ofPoint p).val (coefficientMap (algebraMap R S)) q.val =
      quotientFibreLength (S := S) p q := by
  rw [geometricFibreLength_eq]
  let e := Ideal.quotientEquivAlgOfEq (Laurent S)
    (congrArg (fun J : Ideal (Laurent R) => J.map (coefficientMap (algebraMap R S)))
      (definingIdeal_point p))
  exact (e.toLinearEquiv.baseChange (Laurent S) (Localization.AtPrime q.val) _ _).length_eq

end ScalarMap

end AlgebraicGeometry.Torus.FiniteCorrespondence.Fibre
