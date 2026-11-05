/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Affine
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.Assembly
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.ChartCoefficient

/-! # Original polynomial source geometry with explicit degree-zero input

The affine and qcqs source-cover geometry is independent of the ordinary
source-face proof. This supplier retains only the literal degree-zero
difference epi as an explicit input; it does not assert that input or the
unconditional smooth base-change endpoint.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Full-test source geometry with an explicit original degree-zero difference
epi input, retaining the genuine injective and original cartesian square. -/
theorem higherDirectImage_polynomial_qcqs_injective_positive_isZero_of_difference_epi
    {A : Type u} [CommRing A] {X X' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of (Polynomial A)))
    (g' : X' ⟶ X)
    (H : IsPullback g' f' f (Spec.algebraMap A (Polynomial A)))
    (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I]
    (hEpi : ∀ U V : X.Opens, Epi (sourceEtaleSquareCoefficientComplex f'
      ((etaleOpenSquare U V).map (siteBaseChange g')) ((inverseImage g').obj
        ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I))).g) :
    IsZero ((higherDirectImage f' q).obj ((inverseImage g').obj
      ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I))) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let M := (SheafOfModules.toSheaf (constantRing X Λ)).obj I
  let F := (inverseImage g').obj M
  have hAffine : ∀ U : X.Opens, IsAffineOpen U → SourceOpenPositive g' f' F U := by
    intro U hU r hr
    let : IsAffine U.toScheme := hU
    let T := (opensToEtale X).obj U
    let : IsAffine ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsAffine U.toScheme)
    let J := (moduleInverseImage T.hom Λ).obj I
    let : Injective J := sourceChartModule_injective T Λ I
    have hz := higherDirectImage_polynomial_affine_injective_positive_isZero
      (U := U.toScheme)
      (T.hom ≫ f) (((siteBaseChange g').obj T).hom ≫ f') (pullback.fst T.hom g')
      ((IsPullback.of_hasPullback T.hom g').paste_vert H).flip
      r hr n hn hunit J
    exact hz.of_iso ((higherDirectImage (((siteBaseChange g').obj T).hom ≫ f') r).mapIso
      (sourceChartModuleCoefficientIso g' T Λ I)).symm
  exact higherDirectImage_positive_of_sourceOpenPositive_top g' f' F
    (sourceOpenPositive_of_affine g' f' F hAffine hEpi ⊤ isCompact_univ) q hq

end AlgebraicGeometry.Scheme.EtaleCohomology
