/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.IntegralOpen
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
Native extraction from the R5 Aglib source
`AlgebraicGeometry.SchemeTheoreticImage.FlatOpenBaseChange`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`a706de9a83a360b8fb14f5811b00dff23ee7a6c889982b5aa56a0cda4d29313e`.
Source image-closure comparisons use the actual Mathlib f.image, f.toImage and f.imageι.
  Integral-open, quasi-compactness and flatness hypotheses stay explicit where originally used; no
  nonflat image base change is asserted.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# Flat base change of an integral open image

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Statements, chosen comparisons, and explicit incoming evidence boundaries are retained.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

section IntegralOpenClosureBaseChange

/-! The actual image closure commutes with flat base change. This statement
retains the literal pullback and proves its defining kernel equality; the
pulled-back open need not be integral or connected. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Hom.Image
variable {U X X' : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j] [QuasiCompact j] [IsIntegral U]
  (t : X' ⟶ X)

/-- The actual pulled-back punctured open maps into the literal pullback of
its constructed integral closure. No component comparison is an input. -/
def baseOpenMap : pullback j t ⟶ pullback (AlgebraicGeometry.Scheme.Hom.imageι j) t :=
  pullback.lift (pullback.fst j t ≫ AlgebraicGeometry.Scheme.Hom.toImage j) (pullback.snd j t)
    (by simp only [Category.assoc, openMap_inclusion, pullback.condition])

omit [IsOpenImmersion j] [QuasiCompact j] [IsIntegral U] in
@[reassoc (attr := simp)] lemma baseOpenMap_fst :
    baseOpenMap j t ≫ pullback.fst (AlgebraicGeometry.Scheme.Hom.imageι j) t =
      pullback.fst j t ≫ AlgebraicGeometry.Scheme.Hom.toImage j := pullback.lift_fst ..

omit [IsOpenImmersion j] [QuasiCompact j] [IsIntegral U] in
@[reassoc (attr := simp)] lemma baseOpenMap_snd :
    baseOpenMap j t ≫ pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) t =
      pullback.snd j t := pullback.lift_snd ..

omit [IsOpenImmersion j] [QuasiCompact j] [IsIntegral U] in
lemma baseOpenMap_square :
    IsPullback (pullback.fst j t) (baseOpenMap j t) (AlgebraicGeometry.Scheme.Hom.toImage j)
      (pullback.fst (AlgebraicGeometry.Scheme.Hom.imageι j) t) := by
  have H : IsPullback (pullback.fst j t)
      (baseOpenMap j t ≫ pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) t)
      (AlgebraicGeometry.Scheme.Hom.toImage j ≫ AlgebraicGeometry.Scheme.Hom.imageι j) t := by
    simpa only [baseOpenMap_snd, openMap_inclusion] using
      (IsPullback.of_hasPullback j t)
  exact H.of_bot (baseOpenMap_fst j t).symm
    (IsPullback.of_hasPullback (AlgebraicGeometry.Scheme.Hom.imageι j) t)

instance baseOpenMap_open : IsOpenImmersion (baseOpenMap j t) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (baseOpenMap_square j t) inferInstance

instance baseOpenMap_schemeDominant [Flat t] :
    IsSchemeTheoreticallyDominant (baseOpenMap j t) := by
  let : IsSchemeTheoreticallyDominant (AlgebraicGeometry.Scheme.Hom.toImage j) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  exact IsSchemeTheoreticallyDominant.of_isPullback (baseOpenMap_square j t)

omit [IsOpenImmersion j] in
/-- Scheme-theoretic equality, stronger than an equality of closed supports. -/
lemma baseOpenMap_kernel [Flat t] :
    (pullback.snd j t).ker = (pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) t).ker := by
  rw [← baseOpenMap_snd j t, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- The actual image of the pulled-back punctured open is the pullback of
the actual original closure, with its scheme structure retained. -/
def flatBaseChangeIso [Flat t] :
    (pullback.snd j t).image ≅ pullback (AlgebraicGeometry.Scheme.Hom.imageι j) t := by
  have H : (pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) t).ker =
      (pullback.snd j t).imageι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (baseOpenMap_kernel j t).symm
  let l := IsClosedImmersion.lift (pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) t)
    (pullback.snd j t).imageι H.le
  letI : IsIso l := IsClosedImmersion.isIso_lift _ _ H
  exact asIso l

omit [IsOpenImmersion j] in
@[reassoc (attr := simp)] lemma flatBaseChangeIso_hom_snd [Flat t] :
    (flatBaseChangeIso j t).hom ≫ pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) t =
      (pullback.snd j t).imageι := by
  dsimp only [flatBaseChangeIso, asIso_hom]
  exact IsClosedImmersion.lift_fac ..

omit [IsOpenImmersion j] in
@[reassoc (attr := simp)] lemma toImage_flatBaseChangeIso [Flat t] :
    (pullback.snd j t).toImage ≫ (flatBaseChangeIso j t).hom = baseOpenMap j t := by
  apply (cancel_mono (pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) t)).mp
  simp

omit [IsOpenImmersion j] in
@[reassoc] lemma toImage_flatBaseChangeIso_fst [Flat t] :
    (pullback.snd j t).toImage ≫ (flatBaseChangeIso j t).hom ≫
      pullback.fst (AlgebraicGeometry.Scheme.Hom.imageι j) t = pullback.fst j t ≫
        AlgebraicGeometry.Scheme.Hom.toImage j := by
  simp

end AlgebraicGeometry.Scheme.Hom.Image


end -- noncomputable section
end IntegralOpenClosureBaseChange
