/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AffineFiniteSectionAlgebra
public import Aglib.AlgebraicGeometry.Spec.SmoothSectionPurityTarget
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseOpenBaseChange

/-! # The original smooth-section purity step on schemes

One actual affine neighbourhood of the closed section point retains the
entire local section. Its original section rings instantiate the affine
purity step; the conclusion is transported back through the same native
chart square, not a new normalization or cover.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Scheme-level form of the explicit local section-purity induction step. -/
theorem etaleAt_liftedSection_of_codimensionOne_of_puncturedSection
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)]
    (p : X ⟶ Spec (.of A)) [Smooth p]
    (f : Y ⟶ X) [IsFinite f] [IsDominant f]
    (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (a : Spec (.of A) ⟶ Y) (ha : a ≫ f = s)
    (hdim : 2 ≤ ringKrullDim A)
    (hheight : ∀ x : X, Order.coheight x = 1 →
      ∀ y : Y, f y = x → f.etaleAt y)
    (hpuncture : ∀ x : Spec (.of A), x ∈ puncturedSpecOpen A →
      ∀ y : Y, f y = s x → f.etaleAt y) :
    f.etaleAt (a (IsLocalRing.closedPoint A)) := by
  obtain ⟨V, hV, hc, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s (IsLocalRing.closedPoint A) ∈ (⊤ : X.Opens) from trivial)
  let B := Γ(X, V)
  let U := f ⁻¹ᵁ V
  let C := Γ(Y, U)
  let hU : IsAffineOpen U := hV.preimage f
  let : Nonempty V := ⟨⟨s (IsLocalRing.closedPoint A), hc⟩⟩
  have hac : a (IsLocalRing.closedPoint A) ∈ U := by
    change f (a (IsLocalRing.closedPoint A)) ∈ V
    have he := congrArg (fun g : Spec (.of A) ⟶ X => g (IsLocalRing.closedPoint A)) ha
    exact he.symm ▸ hc
  let : Nonempty U := ⟨⟨a (IsLocalRing.closedPoint A), hac⟩⟩
  let : Algebra A B := (affineSectionCoefficientMap p V).toAlgebra
  let : Algebra B C := LocalNormAlgebra.chartAlgebra f V
  let : Algebra.Smooth A B :=
    RingHom.smooth_algebraMap.mp (affineSectionCoefficientMap_smooth p hV)
  let : Module.Finite B C := LocalNormAlgebra.chart_finite f V hV
  let : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr
    (LocalNormAlgebra.chartMap_injective f V)
  let : IsDomain B := inferInstance
  let : IsDomain C := inferInstance
  let : IsIntegrallyClosed C := isIntegrallyClosed_sections_of_isAffineOpen Y U hU
  let ε : B →ₐ[A] A := affineSectionAugmentation p s hs hV hc
  let δ : C →+* A := affineLocalSectionRetraction a U hac
  have hδ : δ.comp (algebraMap B C) = ε.toRingHom := by
    exact affineFiniteSectionRetraction_comp f s a ha hV hc
  have H : hU.fromSpec ≫ f = Spec.algebraMap B C ≫ hV.fromSpec :=
    (affineFiniteSection_spec f hV).symm
  have hε : Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ hV.fromSpec = s :=
    affineLocalSectionRetraction_spec s hV hc
  have hδspec : Spec.map (CommRingCat.ofHom δ) ≫ hU.fromSpec = a :=
    affineLocalSectionRetraction_spec a hU hac
  have hco : ∀ q : Spec Γ(X, V), Order.coheight (hV.fromSpec q) = q.asIdeal.height :=
    fun q => (coheight_eq_of_isOpenImmersion hV.fromSpec).trans
      (idealHeight_eq_coheight Γ(X, V) q).symm
  have hh : ∀ q : PrimeSpectrum B, q.asIdeal.height = 1 →
      ∀ z : Spec (.of C), Spec.algebraMap B C z = q →
        (Spec.algebraMap B C).etaleAt z := by
    intro q hq z hz
    apply (etaleAt_iff_of_open_square hU.fromSpec _ f hV.fromSpec H z).mpr
    apply hheight (hV.fromSpec q)
    · exact (hco q).trans hq
    · have he := congrArg (fun g : Spec (.of C) ⟶ X => g z) H
      exact he.trans (congrArg hV.fromSpec hz)
  have hp : ∀ x : Spec (.of A), x ∈ puncturedSpecOpen A →
      ∀ z : Spec (.of C), Spec.algebraMap B C z =
        Spec.map (CommRingCat.ofHom ε.toRingHom) x →
        (Spec.algebraMap B C).etaleAt z := by
    intro x hx z hz
    apply (etaleAt_iff_of_open_square hU.fromSpec _ f hV.fromSpec H z).mpr
    apply hpuncture x hx
    have he := congrArg (fun g : Spec (.of C) ⟶ X => g z) H
    exact he.trans ((congrArg hV.fromSpec hz).trans
      (congrArg (fun g : Spec (.of A) ⟶ X => g x) hε))
  have ht := smoothSection_etaleAt_of_codimensionOne_of_puncturedSection
    A B C ε δ hδ hdim hh hp
  have he := congrArg (fun g : Spec (.of A) ⟶ Y => g (IsLocalRing.closedPoint A)) hδspec
  exact he ▸ (etaleAt_iff_of_open_square hU.fromSpec _ f hV.fromSpec H _).mp ht

end AlgebraicGeometry.Scheme.Hom
