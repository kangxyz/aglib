/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Monomials
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GlobalGeneration
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.RingTheory.MvPolynomial.CoordinatePieces

/-!
# Evaluation of homogeneous polynomials on a free sheaf

Let `A` be a ring and `P = P^n_A = ProjectiveSpace A ι`. A family `s : I → A[x]_r` of homogeneous
polynomials of degree `r` defines `homogeneousEvaluation ι r s : 𝒪_P^I ⟶ 𝒪(r)`, sending the
basis section `e_i` of the free sheaf to the section `s i` of `𝒪(r)` (`homogeneousSectionFamily`,
`homogeneousEvaluation_freeSection`); for the coordinate powers `x_i^r` it is
`coordinatePowerGeneratingMap` (`homogeneousEvaluation_coordinatePower`).

For the monomials `x^a` of degree `r` (`Monomials ι r`), the family `monomialFamily` is the
monomial basis `MvPolynomial.homogeneousPieceBasis` of `A[x]_r`, and its evaluation is the
**monomial map** `monomialMap ι A r : 𝒪^{monomials} ⟶ 𝒪(r)`. The basis element of `x^a` goes to
the global section `x^a` (`monomialSection`, `ιFree_monomialMap`).

The monomial map is `W ⊗ Sym^r V ⟶ E(r)` of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §5, p. 26, for `E = 𝒪`, written in the monomial basis. Its adjoints over a
base `T` are the quotient `π_{T*} E_T(r) → π_{T*} F(r)` (`HilbertScheme/DirectImageSheafQuotient`)
and the evaluation `h` whose image cuts out the universal subscheme
(`HilbertScheme/UniversalSubscheme`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A]

/-- **Evaluation of homogeneous polynomials** `𝒪_P^I ⟶ 𝒪(r)`: the basis section `e_i` of the free
sheaf goes to the global section `s i` of `𝒪(r)`. -/
def homogeneousEvaluation (r : ℕ) {I : Type u} (s : I → homogeneousSubmodule ι A r) :
    SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) I ⟶ twistingSheaf A ι (r : ℤ) :=
  (twistingSheaf A ι (r : ℤ)).freeHomEquiv.symm (fun i => homogeneousSectionFamily A ι r (s i))

/-- The evaluation sends each basis section to its homogeneous polynomial section. -/
theorem homogeneousEvaluation_freeSection (r : ℕ) {I : Type u}
    (s : I → homogeneousSubmodule ι A r) (i : I) (V : (ProjectiveSpace A ι).Opens) :
    (homogeneousEvaluation ι r s).val.app (Opposite.op V)
        ((SheafOfModules.freeSection (R := (ProjectiveSpace A ι).ringCatSheaf) i).val
          (Opposite.op V)) =
      (homogeneousSectionFamily A ι r (s i)).val (Opposite.op V) :=
  congrArg (fun t : (twistingSheaf A ι (r : ℤ)).sections => t.val (Opposite.op V))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun j => homogeneousSectionFamily A ι r (s j)) i)

/-- For the coordinate powers `x_i^r`, the evaluation is `coordinatePowerGeneratingMap`. -/
theorem homogeneousEvaluation_coordinatePower (r : ℕ) :
    homogeneousEvaluation ι r (coordinatePower A ι r) = coordinatePowerGeneratingMap A ι r :=
  rfl

/-- The compatible family of a homogeneous polynomial section is the family of restrictions of the
global section. -/
theorem homogeneousSectionFamily_eq (r : ℕ) (p : homogeneousSubmodule ι A r) :
    homogeneousSectionFamily A ι r p =
      (((twistingSheaf A ι (r : ℤ)).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}
        ).sectionsEquivOfIsInitial (isTerminalTop (α := (ProjectiveSpace A ι).Opens)).op
          ).symm (homogeneousSection A ι r p) :=
  Subtype.ext (funext fun _ => rfl)

/-- **The monomials** `x^a` of degree `r`: the monomial basis `homogeneousPieceBasis` of the
homogeneous polynomials of degree `r`. -/
def monomialFamily (r : ℕ) : Monomials ι r → homogeneousSubmodule ι A r :=
  homogeneousPieceBasis (ι := ι) A r

theorem monomialFamily_apply (r : ℕ) (a : Monomials ι r) :
    monomialFamily (A := A) ι r a = homogeneousPieceBasis (ι := ι) A r a :=
  rfl

/-- The monomial `x^a` as a polynomial. -/
theorem monomialFamily_apply_coe (r : ℕ) (a : Monomials ι r) :
    (monomialFamily (A := A) ι r a : MvPolynomial ι A) = monomial a.1 1 :=
  homogeneousPieceBasis_val A r a

variable (A)

/-- The global section of `𝒪(r)` on `P^n_A` of the monomial `x^a`. -/
def monomialSection (r : ℕ) (a : Monomials ι r) : Γ(twistingSheaf A ι (r : ℤ), ⊤) :=
  homogeneousSection A ι r (homogeneousPieceBasis (ι := ι) A r a)

/-- **The monomial map** `𝒪^{monomials} ⟶ 𝒪(r)` on `P^n_A`: the evaluation of the monomials; the
basis element of `x^a` goes to the section `x^a` (`ιFree_monomialMap`). -/
def monomialMap (r : ℕ) :
    SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) (Monomials ι r) ⟶
      twistingSheaf A ι r :=
  homogeneousEvaluation ι r (monomialFamily (A := A) ι r)

/-- The evaluation of the monomial family is the monomial map. -/
theorem homogeneousEvaluation_monomialFamily (r : ℕ) :
    homogeneousEvaluation ι r (monomialFamily (A := A) ι r) = monomialMap ι A r :=
  rfl

/-- The monomial map sends the basis element of `x^a` to the global section `x^a`. -/
theorem ιFree_monomialMap (r : ℕ) (a : Monomials ι r) :
    SheafOfModules.ιFree a ≫ monomialMap ι A r =
      (Scheme.Modules.unitHomGlobalSectionsEquiv (ProjectiveSpace A ι) (twistingSheaf A ι r)).symm
        (monomialSection ι A r a) :=
  (Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan _)
    (fun i => (twistingSheaf A ι (r : ℤ)).unitHomEquiv.symm
      (homogeneousSectionFamily A ι r (monomialFamily (A := A) ι r i))) a).trans
    (congrArg (twistingSheaf A ι (r : ℤ)).unitHomEquiv.symm
      (homogeneousSectionFamily_eq ι r (monomialFamily (A := A) ι r a)))

end AlgebraicGeometry.ProjectiveSpace
