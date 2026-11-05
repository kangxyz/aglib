/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.PolynomialGeometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.DifferenceEpi
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.ZMod
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.PolynomialTower

/-! # Proposed original qcqs polynomial vanishing assembly

This source draft assembles the affine theorem, native original-coefficient
restriction, ordinary source-face naturality, relative Mayer–Vietoris and
binary source induction. It is not an accepted endpoint until its complete
native dependency chain and this file have passed exact compilation.
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

/-- Proposed full-test polynomial vanishing on the original qcqs coefficient
source, retaining the genuine ringed injective and original cartesian square. -/
theorem higherDirectImage_polynomial_qcqs_injective_positive_isZero
    {A : Type u} [CommRing A] {X X' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of (Polynomial A)))
    (g' : X' ⟶ X)
    (H : IsPullback g' f' f (Spec.algebraMap A (Polynomial A)))
    (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I] :
    IsZero ((higherDirectImage f' q).obj ((inverseImage g').obj
      ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I))) := by
  let : Smooth (Spec.algebraMap A (Polynomial A)) :=
    inferInstanceAs (Smooth (PolynomialLaurent.polynomialProjection (.of A)))
  let Λ := ULift.{u + 1} (ZMod n)
  let M := (SheafOfModules.toSheaf (constantRing X Λ)).obj I
  let F := (inverseImage g').obj M
  have hM : n • 𝟙 M = 0 :=
    Functor.map_nsmul_id_eq_zero (SheafOfModules.toSheaf (constantRing X Λ)) I n
      (ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero X.smallEtaleTopology n I)
  have hEpi : ∀ U V : X.Opens, Epi (sourceEtaleSquareCoefficientComplex f'
      ((etaleOpenSquare U V).map (siteBaseChange g')) F).g := by
    intro U V
    let Q := etaleOpenSquare U V
    let : Mono Q.f₂₄ := etaleOpenSquare_f₂₄_mono U V
    let : Mono Q.f₃₄ := etaleOpenSquare_f₃₄_mono U V
    let : Mono Q.f₁₃ := inferInstanceAs
      (Mono ((opensToEtale X).map (homOfLE inf_le_right : U ⊓ V ⟶ V)))
    let : Epi ((sourceEtaleImageMap f Q.f₁₃).app M) :=
      sourceEtaleImageMap_epi_of_ringed_injective f Q.f₁₃ Λ I
    exact sourceEtaleSquare_difference_epi f f' (Spec.algebraMap A (Polynomial A))
      g' H Q M n hn hM
  exact higherDirectImage_polynomial_qcqs_injective_positive_isZero_of_difference_epi
    f f' g' H q hq n hn hunit I hEpi

end AlgebraicGeometry.Scheme.EtaleCohomology
