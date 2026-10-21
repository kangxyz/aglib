/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
Native extraction from the R5 Aglib source
`AlgebraicGeometry.SchemeTheoreticImage.IntegralOpen`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`f647cb257e23f20a9a4466fe8f5ab276cce9ad31b4270886128d5f03eef9b8b2`.
Source image-closure comparisons use the actual Mathlib f.image, f.toImage and f.imageι.
  Integral-open, quasi-compactness and flatness hypotheses stay explicit where originally used; no
  nonflat image base change is asserted.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# The closed image of an integral open immersion

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Statements, chosen comparisons, and explicit incoming evidence boundaries are retained.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

section AlgebraicGeometry.Scheme.Hom.Image

/-! The reduced closed closure of an actual nonempty integral open immersion.
The construction is its scheme-theoretic image; reducedness is proved rather
than assumed. No irreducible component, normalization, or cycle is supplied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Hom.Image
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [IsIntegral U]

omit [IsOpenImmersion j] in
lemma kernel_radical : j.ker.radical = j.ker := by
  ext V : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  exact Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot.comap (j.app V.1).hom)

instance closure_reduced : IsReduced (AlgebraicGeometry.Scheme.Hom.image j) := by
  apply AlgebraicGeometry.Scheme.IdealSheafData.subscheme_reduced_of_radical
  exact kernel_radical j

instance closure_integral : IsIntegral (AlgebraicGeometry.Scheme.Hom.image j) :=
  AlgebraicGeometry.Scheme.schemeImage_isIntegral j

omit [IsOpenImmersion j] [IsIntegral U] in
lemma inclusion_range : Set.range (AlgebraicGeometry.Scheme.Hom.imageι j) = closure (Set.range j)
  := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

instance openMap_open : IsOpenImmersion (AlgebraicGeometry.Scheme.Hom.toImage j) := by
  let t : U ⟶ pullback (AlgebraicGeometry.Scheme.Hom.imageι j) j :=
    pullback.lift (AlgebraicGeometry.Scheme.Hom.toImage j) (𝟙 U)
      (by simpa only [Category.id_comp] using j.toImage_imageι)
  have ht : t ≫ pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) j = 𝟙 U := by simp [t]
  have : Surjective (pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) j) := by
    constructor
    intro x
    exact ⟨t x, by simpa using congrArg (fun f : U ⟶ U => f x) ht⟩
  let : IsIso (pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) j) :=
    isIso_of_isClosedImmersion_of_surjective _
  have h : AlgebraicGeometry.Scheme.Hom.toImage j = inv (pullback.snd
    (AlgebraicGeometry.Scheme.Hom.imageι j) j) ≫ pullback.fst (AlgebraicGeometry.Scheme.Hom.imageι
    j) j := by
    have ht' : t = inv (pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) j) := by
      apply (cancel_mono (pullback.snd (AlgebraicGeometry.Scheme.Hom.imageι j) j)).mp
      simpa using ht
    rw [← ht']
    simp [t]
  rw [h]
  infer_instance

omit [IsOpenImmersion j] [QuasiCompact j] [IsIntegral U] in
@[reassoc] lemma openMap_inclusion : AlgebraicGeometry.Scheme.Hom.toImage j ≫
  AlgebraicGeometry.Scheme.Hom.imageι j = j :=
  j.toImage_imageι

instance closure_proper {S : Scheme.{u}} (b : X ⟶ S) [IsProper b] :
    IsProper (AlgebraicGeometry.Scheme.Hom.imageι j ≫ b) := by infer_instance

end AlgebraicGeometry.Scheme.Hom.Image

end -- noncomputable section
end AlgebraicGeometry.Scheme.Hom.Image
