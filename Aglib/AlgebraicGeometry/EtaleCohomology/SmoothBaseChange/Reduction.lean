/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Bounded
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.LocalCoordinates
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.PolynomialTower

/-! # Reduction of smooth exchange to the original affine-line projections

This is a reduction, not the positive-dimensional smooth base-change theorem.
Its remaining input is the original all-degree affine-line comparison for
qcqs direct image and coefficients killed by a modulus invertible on the
entire base. The existing `Proper.boundedExchange` supplies the shared exact
square test, with no properness assumption. Actual smooth coordinates,
polynomial tower equations, original horizontal pasting and actual target
locality prove the reduction. No smooth-acyclicity field is used.

Intermediate tests use the native standard models. The final original-map
corollary uses the accepted actual model transport and retains four independent
derived-category models and universes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v dX dS dX' dS'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.SmoothReduction

attribute [local instance] hasSheafifyLarge

/-- The explicit original all-degree comparison family for one modulus.
The square test is the existing bounded exchange, not a new smooth hypothesis. -/
def UniformHigherBaseChange (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) : Prop :=
  ∀ {X X' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g), QuasiCompact f → QuasiSeparated f →
      IsUnit (n : Γ(S, ⊤)) → Proper.boundedExchange n f f' g g' h.w.symm

variable {n : ℕ}

/-- The actual arbitrary-square étale theorem supplies the entire comparison family. -/
theorem uniformHigherBaseChange_etale {S' S : Scheme.{u}} (g : S' ⟶ S) [Etale g] :
    UniformHigherBaseChange n g := by
  intro X X' f f' g' h _ _ _
  exact boundedExchange_etale n f f' g g' h

/-- Native horizontal pasting makes the exact uniform comparison family
stable under composition. The actual lift triangle is retained before
substitution; the original exchange test stays at one shared head. -/
theorem UniformHigherBaseChange.comp {S₀ S₁ S₂ : Scheme.{u}}
    {g₁ : S₁ ⟶ S₀} {g₂ : S₂ ⟶ S₁}
    (h₁ : UniformHigherBaseChange n g₁) (h₂ : UniformHigherBaseChange n g₂) :
    UniformHigherBaseChange n (g₂ ≫ g₁) := by
  intro X X₂ f f₂ k h hf hqs hn
  have : QuasiCompact f := hf
  have : QuasiSeparated f := hqs
  let a : X₂ ⟶ pullback f g₁ :=
    pullback.lift k (f₂ ≫ g₂) (by simpa only [Category.assoc] using h.w)
  have ha : a ≫ pullback.fst f g₁ = k := pullback.lift_fst _ _ _
  have hb : a ≫ pullback.snd f g₁ = f₂ ≫ g₂ := pullback.lift_snd _ _ _
  clear_value a
  subst k
  have H₁ : IsPullback (pullback.fst f g₁) (pullback.snd f g₁) f g₁ :=
    IsPullback.of_hasPullback f g₁
  have H₂ : IsPullback a f₂ (pullback.snd f g₁) g₂ := h.of_right hb H₁
  have hn₁ : IsUnit (n : Γ(S₁, ⊤)) := by
    simpa only [map_natCast] using hn.map g₁.appTop.hom
  exact boundedExchange_hComp n f (pullback.snd f g₁) f₂ g₁ g₂
    (pullback.fst f g₁) a H₁.w.symm H₂.w.symm h.w.symm
    (h₁ f (pullback.snd f g₁) (pullback.fst f g₁) H₁ hf hqs hn)
    (h₂ (pullback.snd f g₁) f₂ a H₂ inferInstance inferInstance hn₁)

/-- The exact comparison family descends from an actual jointly surjective
étale cover of the source of the base morphism, namely the target of exchange. -/
theorem uniformHigherBaseChange_of_etaleCover {S' S : Scheme.{u}} (g : S' ⟶ S)
    {ι : Type v} (U : ι → S'.Etale)
    (hU : ∀ s : S', ∃ (i : ι) (x : (U i).left), (U i).hom x = s)
    (h : ∀ i, UniformHigherBaseChange n ((U i).hom ≫ g)) :
    UniformHigherBaseChange n g := by
  intro X X' f f' k H hf hqs hn
  let Y := fun i => pullback f' (U i).hom
  let p := fun i => pullback.snd f' (U i).hom
  let a := fun i => pullback.fst f' (U i).hom
  have Hp (i : ι) : IsPullback (a i) (p i) f' (U i).hom :=
    IsPullback.of_hasPullback f' (U i).hom
  have Hc (i : ι) : p i ≫ ((U i).hom ≫ g) = (a i ≫ k) ≫ f :=
    ((Hp i).paste_horiz H).w.symm
  exact boundedExchange_of_etaleCover n f f' g k H.w.symm U hU Y p a Hp Hc
    (fun i => h i f (p i) (a i ≫ k) ((Hp i).paste_horiz H) hf hqs hn)

/-- Exact finite polynomial towers reduce all finite-variable projections to
one-variable projections. The dimension-zero base case is an actual isomorphism. -/
theorem uniformHigherBaseChange_mvPolynomial_of_line
    (hline : ∀ R : CommRingCat.{u},
      UniformHigherBaseChange n (PolynomialLaurent.polynomialProjection R))
    (R : CommRingCat.{u}) (r : ℕ) :
    UniformHigherBaseChange n
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))) := by
  induction r with
  | zero => exact @uniformHigherBaseChange_etale _ _ _ _ inferInstance
  | succ r ih =>
    rw [← PolynomialLaurent.mvPolynomialSuccIso_projection R r]
    have he : UniformHigherBaseChange n (PolynomialLaurent.mvPolynomialSuccIso R r).hom :=
      @uniformHigherBaseChange_etale _ _ _ _ inferInstance
    have hstep : UniformHigherBaseChange n
        ((PolynomialLaurent.mvPolynomialSuccIso R r).hom ≫
          PolynomialLaurent.polynomialProjection (.of (MvPolynomial (Fin r) R))) :=
      UniformHigherBaseChange.comp (hline (.of (MvPolynomial (Fin r) R))) he
    have htotal : UniformHigherBaseChange n
        (((PolynomialLaurent.mvPolynomialSuccIso R r).hom ≫
          PolynomialLaurent.polynomialProjection (.of (MvPolynomial (Fin r) R))) ≫
            Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin r) R))) :=
      UniformHigherBaseChange.comp ih hstep
    rw [Category.assoc] at htotal
    exact @htotal

/-- Actual smooth charts reduce original all-degree uniform-modulus exchange
to the affine-line projection comparison. The latter remains a genuine
positive-dimensional theorem, not a field silently supplied by this result. -/
theorem uniformHigherBaseChange_smooth_of_line
    (hline : ∀ R : CommRingCat.{u},
      UniformHigherBaseChange n (PolynomialLaurent.polynomialProjection R))
    {S' S : Scheme.{u}} (g : S' ⟶ S) [Smooth g] :
    UniformHigherBaseChange n g := by
  let U : S' → S'.Etale := fun x =>
    Scheme.Etale.mk (SmoothLocalCoordinates.chart g x).sourceMap
  have hU : ∀ s : S', ∃ (i : S') (x : (U i).left), (U i).hom x = s := by
    intro s
    exact ⟨s, (SmoothLocalCoordinates.chart g s).mem_range_sourceMap⟩
  apply uniformHigherBaseChange_of_etaleCover g U hU
  intro x
  let c := SmoothLocalCoordinates.chart g x
  change UniformHigherBaseChange n (c.sourceMap ≫ g)
  rw [← c.factorization]
  have ht : UniformHigherBaseChange n c.targetMap :=
    @uniformHigherBaseChange_etale _ _ _ _ inferInstance
  have he : UniformHigherBaseChange n c.coordinateMap :=
    @uniformHigherBaseChange_etale _ _ _ _ inferInstance
  have hp : UniformHigherBaseChange n c.projection :=
    uniformHigherBaseChange_mvPolynomial_of_line hline Γ(S, c.targetOpen) c.dimension
  have hpe : UniformHigherBaseChange n (c.coordinateMap ≫ c.projection) :=
    UniformHigherBaseChange.comp hp he
  have htotal : UniformHigherBaseChange n
      ((c.coordinateMap ≫ c.projection) ≫ c.targetMap) :=
    UniformHigherBaseChange.comp ht hpe
  rw [Category.assoc] at htotal
  exact @htotal

/-- The reduction at the original higher exchange in four independently
supplied derived models. Actual model transport is used, not identification
of the models or replacement of the original comparison. -/
theorem higherBaseChangeMap_smooth_isIso_of_line
    (hline : ∀ R : CommRingCat.{u},
      UniformHigherBaseChange n (PolynomialLaurent.polynomialProjection R))
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f] [Smooth g]
    (hn : IsUnit (n : Γ(S, ⊤))) (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' h.w.symm q).app F) := by
  simpa only [higherBaseChangeMapFromDerived_eq] using
    (Proper.higherBaseChangeMap_isIso_of_boundedExchange.{u, dX, dS, dX', dS'}
      f f' g g' h.w.symm n
      (uniformHigherBaseChange_smooth_of_line hline g f f' g' h
        inferInstance inferInstance hn) F hF q)

end AlgebraicGeometry.Scheme.EtaleCohomology.SmoothReduction
