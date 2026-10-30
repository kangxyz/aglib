/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparison

/-! # Original comparison on whole pullback-map values

The comparisons are constructed by `originalExtSourceComparison`. The supplied
pullback families and exchange transformation are identified with their original
definitions before a coefficient or degree is selected. The whole conjugate map
is then proved equal to the supplied target family from the original source and
mate laws. Invertibility is needed only for the selected exchange component.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe uI uC vC uE vE uD vD uV vV

/-- Transport the complete original inverse-source composition before any
concrete indexing arrow or coefficient model is substituted. The input is the
original composition law at the equal target index. -/
theorem sourceInverse_composite_transport
    {I : Type uI} {C : Type uC} [Category.{vC} C]
    {E : Type uE} [Category.{vE} E] {D : Type uD} [Category.{vD} D]
    {V : Type uV} [Category.{vV} V]
    (K : I → C ⥤ D) {T : V ⥤ C} {R : V ⥤ E} {S : V ⥤ D}
    (q : ∀ i, T ⋙ K i ≅ S) {i j : I} (h : i = j)
    {F : C ⥤ E} {G : E ⥤ D} (e : T ⋙ F ≅ R) (e' : R ⋙ G ≅ S)
    (c : K j ≅ F ⋙ G) (A : V)
    (hc : (q j).inv.app A ≫ c.hom.app (T.obj A) =
      e'.inv.app A ≫ G.map (e.inv.app A)) :
    ((q i).app A).inv ≫
        (eqToIso (congrArg K h) ≪≫ c).hom.app (T.obj A) =
      (e'.app A).inv ≫ G.map (e.app A).inv := by
  cases h
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.app_inv] using hc

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

universe u₀ v₀ e₀ u₁ v₁ e₁ u₂ v₂ e₂ u₃ v₃ e₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{e₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{e₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{e₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{e₃} C₃]
  {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {L' : C₂ ⥤ C₃} {R' : C₃ ⥤ C₂}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (adj : L ⊣ R) (adj' : L' ⊣ R')
  (G : C₀ ⥤ C₂) (H : C₁ ⥤ C₃)
  {U₀ : C₀} {U₁ : C₁} {U₂ : C₂} {U₃ : C₃}
  (e : L.obj U₀ ≅ U₁) (e' : L'.obj U₂ ≅ U₃)

/-- The whole conjugate family uses the actual adjoint/source comparisons and
the supplied original base pullback and exchange values. -/
def originalExtSourceComparisonConjugate
    (β : R ⋙ G ⟶ H ⋙ R')
    (pG : (N : C₀) → (n : ℕ) → Ext.{e₀} U₀ N n →+ Ext.{e₂} U₂ (G.obj N) n)
    (M : C₁) (n : ℕ) : Ext.{e₁} U₁ M n →+ Ext.{e₃} U₃ (H.obj M) n :=
  let E := originalExtSourceComparison adj e M n
  let E' := originalExtSourceComparison adj' e' (H.obj M) n
  E'.toAddMonoidHom.comp
    (((Ext.mk₀ (β.app M)).postcomp U₂ (add_zero n)).comp
      ((pG (R.obj M) n).comp E.symm.toAddMonoidHom))

/-- Evaluation retains exactly the two constructed comparisons and original
coefficient postcomposition. -/
theorem originalExtSourceComparisonConjugate_apply
    (β : R ⋙ G ⟶ H ⋙ R')
    (pG : (N : C₀) → (n : ℕ) → Ext.{e₀} U₀ N n →+ Ext.{e₂} U₂ (G.obj N) n)
    (M : C₁) (n : ℕ) (a : Ext.{e₁} U₁ M n) :
    originalExtSourceComparisonConjugate adj adj' G H e e' β pG M n a =
      originalExtSourceComparison adj' e' (H.obj M) n
        ((pG (R.obj M) n ((originalExtSourceComparison adj e M n).symm a)).comp
          (Ext.mk₀ (β.app M)) (add_zero n)) := rfl

/-- Bijectivity of the constructed conjugate requires the original base map
and only the selected exchange component to be invertible. -/
theorem originalExtSourceComparisonConjugate_bijective
    (β : R ⋙ G ⟶ H ⋙ R')
    (pG : (N : C₀) → (n : ℕ) → Ext.{e₀} U₀ N n →+ Ext.{e₂} U₂ (G.obj N) n)
    (M : C₁) (n : ℕ) [IsIso (β.app M)]
    (hG : Function.Bijective (pG (R.obj M) n)) :
    Function.Bijective
      (originalExtSourceComparisonConjugate adj adj' G H e e' β pG M n) := by
  let E := originalExtSourceComparison adj e M n
  let E' := originalExtSourceComparison adj' e' (H.obj M) n
  change Function.Bijective (fun a : Ext.{e₁} U₁ M n =>
    E' ((pG (R.obj M) n (E.symm a)).comp (Ext.mk₀ (β.app M)) (add_zero n)))
  exact E'.bijective.comp
    ((((extFunctorObj U₂ n).mapIso (asIso (β.app M))).addCommGroupIsoToAddEquiv.bijective).comp
      (hG.comp E.symm.bijective))

variable [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (L₀ : C₀ ⥤ C₃) [L₀.Additive]
  [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
  (c : L₀ ≅ G ⋙ L') (d : L₀ ≅ L ⋙ H)
  (sG : U₂ ⟶ G.obj U₀) (sH : U₃ ⟶ H.obj U₁) (s₀ : U₃ ⟶ L₀.obj U₀)
  (hs : s₀ ≫ c.hom.app U₀ = e'.inv ≫ L'.map sG)
  (ht : s₀ ≫ d.hom.app U₀ = sH ≫ H.map e.inv)

include hs ht in
/-- The whole original mate and source equations determine the whole family
of additive maps, before coefficient and degree substitution. -/
theorem originalExtSourceComparisonConjugate_eq
    (β : R ⋙ G ⟶ H ⋙ R')
    (hβ : β = (mateEquiv adj adj'
      (TwoSquare.mk G L L' H (c.symm ≪≫ d).hom)).natTrans)
    (pG : (N : C₀) → (n : ℕ) → Ext.{e₀} U₀ N n →+ Ext.{e₂} U₂ (G.obj N) n)
    (hpG : pG = fun N n => G.extPrecompMap sG N n)
    (pH : (M : C₁) → (n : ℕ) → Ext.{e₁} U₁ M n →+ Ext.{e₃} U₃ (H.obj M) n)
    (hpH : pH = fun M n => H.extPrecompMap sH M n) :
    originalExtSourceComparisonConjugate adj adj' G H e e' β pG = pH := by
  subst pG
  subst pH
  subst β
  funext M n
  apply AddMonoidHom.ext
  intro a
  rw [originalExtSourceComparisonConjugate_apply]
  let E := originalExtSourceComparison adj e M n
  have h := originalExtSourceComparison_mate_square adj adj' G H L₀ c d
    e e' sG sH s₀ hs ht M n (E.symm a)
  exact h.trans (congrArg (H.extPrecompMap sH M n) (E.apply_symm_apply a))

include hs ht in
/-- Transfer bijectivity on the supplied original map values. Their defining
equalities, not a desired cohomology square, are the additional inputs. -/
theorem originalExtSourceComparison_bijective_of_mate_values
    (β : R ⋙ G ⟶ H ⋙ R')
    (hβ : β = (mateEquiv adj adj'
      (TwoSquare.mk G L L' H (c.symm ≪≫ d).hom)).natTrans)
    (pG : (N : C₀) → (n : ℕ) → Ext.{e₀} U₀ N n →+ Ext.{e₂} U₂ (G.obj N) n)
    (hpG : pG = fun N n => G.extPrecompMap sG N n)
    (pH : (M : C₁) → (n : ℕ) → Ext.{e₁} U₁ M n →+ Ext.{e₃} U₃ (H.obj M) n)
    (hpH : pH = fun M n => H.extPrecompMap sH M n)
    (M : C₁) (n : ℕ) [IsIso (β.app M)]
    (hG : Function.Bijective (pG (R.obj M) n)) :
    Function.Bijective (pH M n) := by
  have h := originalExtSourceComparisonConjugate_eq adj adj' G H e e' L₀ c d
    sG sH s₀ hs ht β hβ pG hpG pH hpH
  rw [← h]
  exact originalExtSourceComparisonConjugate_bijective adj adj' G H e e' β pG M n hG

end CategoryTheory.Adjunction
