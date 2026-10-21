/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.FlatOpenBaseChange

/-!
Native extraction from the R5 Aglib source
`AlgebraicGeometry.SchemeTheoreticImage.OpenComparison`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`845aa9a17bbad55fa384e494481986b29fce8bedebc2016861543114ade156b3`.
Source image-closure comparisons use the actual Mathlib f.image, f.toImage and f.imageι.
  Integral-open, quasi-compactness and flatness hypotheses stay explicit where originally used; no
  nonflat image base change is asserted.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# Comparing open images and excluding flat charts

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Statements, chosen comparisons, and explicit incoming evidence boundaries are retained.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

section StrictClosureOpenComparison

/-! Two exact auxiliary steps for matching actual strict-transform charts:
open immersions with the same range have the same scheme-theoretic image,
and a flat chart disjoint from the punctured open has empty closure pullback.
Neither statement identifies arbitrary closed subschemes by their support. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Hom.Image

variable {U V X : Scheme.{u}} (j : U ⟶ X) (q : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion q]

/-- The scheme structures agree because the maps are open immersions, not
because arbitrary closed subschemes with equal support are equal. -/
lemma open_kernel_eq_of_range_eq (h : Set.range j = Set.range q) : j.ker = q.ker := by
  let e := IsOpenImmersion.isoOfRangeEq j q h
  have he : e.hom ≫ q = j := IsOpenImmersion.isoOfRangeEq_hom_fac j q h
  rw [← he, Scheme.Hom.ker_comp_of_isIso]

/-- Canonical actual-image comparison retaining the AlgebraicGeometry.Scheme.Hom.imageι into X. -/
def openImageIso (h : Set.range j = Set.range q) : j.image ≅ q.image := by
  have H : q.imageι.ker = j.imageι.ker := by
    simp only [Scheme.IdealSheafData.ker_subschemeι]
    exact (open_kernel_eq_of_range_eq j q h).symm
  let l := IsClosedImmersion.lift q.imageι j.imageι H.le
  letI : IsIso l := IsClosedImmersion.isIso_lift _ _ H
  exact asIso l

@[reassoc (attr := simp)] lemma openImageIso_hom_inclusion
    (h : Set.range j = Set.range q) : (openImageIso j q h).hom ≫ q.imageι = j.imageι := by
  dsimp only [openImageIso, asIso_hom]
  exact IsClosedImmersion.lift_fac ..

@[reassoc] lemma openImageIso_open (h : Set.range j = Set.range q) :
    j.toImage ≫ (openImageIso j q h).hom =
      (IsOpenImmersion.isoOfRangeEq j q h).hom ≫ q.toImage := by
  apply (cancel_mono q.imageι).mp
  simp

variable {X' : Scheme.{u}} [QuasiCompact j] [IsIntegral U]
  (t : X' ⟶ X) [Flat t] [IsEmpty (pullback (C := Scheme.{u}) j t)]

/-- A chart missing the literal punctured open also misses its actual
closed closure after flat pullback, scheme-theoretically. -/
instance flatClosurePullback_empty : IsEmpty (pullback (C := Scheme.{u})
  (AlgebraicGeometry.Scheme.Hom.imageι j) t) := by
  have : IsEmpty (pullback.snd (C := Scheme.{u}) j t).image := by
    change IsEmpty (pullback.snd (C := Scheme.{u}) j t).ker.subscheme
    rw [Scheme.ker_eq_top_of_isEmpty]
    infer_instance
  exact Function.isEmpty (flatBaseChangeIso j t).inv

end AlgebraicGeometry.Scheme.Hom.Image

namespace AlgebraicGeometry.Scheme.Hom.Image
variable {U X Z Y P : Scheme.{u}} (j : U ⟶ X)
  [hOpen : IsOpenImmersion j] [QuasiCompact j] [IsIntegral U]
  (t : Z ⟶ X) [Flat t] (q : X ⟶ Y) (p : P ⟶ Y) (s : Z ⟶ P)

omit hOpen in
/-- A full scheme-valued contraction triangle into a locus disjoint from
the original punctured image excludes the entire flat chart from the actual
strict closure, including its scheme structure. -/
lemma flatClosurePullback_empty_of_contraction
    {U X Z Y P : Scheme.{u}} (j : U ⟶ X)
    [QuasiCompact j] [IsIntegral U]
    (t : Z ⟶ X) [Flat t] (q : X ⟶ Y) (p : P ⟶ Y) (s : Z ⟶ P)
    (ht : t ≫ q = s ≫ p)
    (hj : Disjoint (Set.range (j ≫ q)) (Set.range p)) :
    IsEmpty (pullback (C := Scheme.{u}) (AlgebraicGeometry.Scheme.Hom.imageι j) t) := by
  have : IsEmpty (pullback (C := Scheme.{u}) j t) := by
    constructor
    intro z
    have H := congrArg (fun f => f z) (pullback.condition (f := j) (g := t))
    have H' := congrArg (fun f => f (pullback.snd j t z)) ht
    apply Set.disjoint_left.mp hj ⟨pullback.fst j t z, rfl⟩
    exact ⟨s (pullback.snd j t z), H'.symm.trans (congrArg q H.symm)⟩
  exact flatClosurePullback_empty j t

end AlgebraicGeometry.Scheme.Hom.Image

end -- noncomputable section
end StrictClosureOpenComparison
