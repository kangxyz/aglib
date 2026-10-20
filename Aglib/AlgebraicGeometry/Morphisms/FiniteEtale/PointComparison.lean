/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-!
# Actual points through a finite-etale base-change comparison

These equations retain the original point and the displayed comparison's
inverse, followed by the literal pullback projection. The existing
`fiberBaseChangeEquiv` supplies the point-lift equivalence; no new carrier or
point-equivalence implementation is introduced here. The equations work with
any test scheme and any supplied actual comparison isomorphism.

Source: unmarked point-comparison slices of
`R5Lab.AlgebraicGeometry.Curves.LocalModels.CyclicCovers.OneGonLift:132–211`,
R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e26ed93e094ea09b9e080a7b913bd0dc919b073c13f03654768a1c687dd5aca3`.
The model section in that source is the existing
`SectionLifting.henselianPointAboveSection`; its original universal comparison
premise remains conditional and is not discharged here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.Lifting

universe u
variable {S T U : Scheme.{u}} (i : S ⟶ T)
  (C : FiniteEtale T) (C₀ : FiniteEtale S) (e : (baseChange i).obj C ≅ C₀)
  (s : U ⟶ C₀.obj.left)

/-- Projecting the point through the specified inverse comparison retains
its original structural triangle. -/
@[reassoc] theorem comparisonPoint_over :
    (s ≫ e.inv.hom.left ≫ pullback.fst C.obj.hom i) ≫ C.obj.hom =
      (s ≫ C₀.obj.hom) ≫ i := by
  have hw := Over.w e.inv.hom
  change e.inv.hom.left ≫ pullback.snd C.obj.hom i = C₀.obj.hom at hw
  simp only [Category.assoc, pullback.condition]
  rw [← Category.assoc e.inv.hom.left, hw]

/-- The literal pullback lift of the projected point is the original point
followed by this comparison's inverse. -/
theorem comparisonPoint_pullback :
    pullback.lift (s ≫ e.inv.hom.left ≫ pullback.fst C.obj.hom i)
      (s ≫ C₀.obj.hom) (comparisonPoint_over i C C₀ e s) = s ≫ e.inv.hom.left := by
  have hw := Over.w e.inv.hom
  change e.inv.hom.left ≫ pullback.snd C.obj.hom i = C₀.obj.hom at hw
  apply pullback.hom_ext
  · simp only [pullback.lift_fst, Category.assoc]
  · simp only [pullback.lift_snd, Category.assoc, hw]

/-- The actual point is recovered under the same forward comparison.
This is equality of the original scheme morphisms. -/
@[reassoc] theorem comparisonPoint_compare :
    pullback.lift (s ≫ e.inv.hom.left ≫ pullback.fst C.obj.hom i)
      (s ≫ C₀.obj.hom) (comparisonPoint_over i C C₀ e s) ≫ e.hom.hom.left = s := by
  rw [comparisonPoint_pullback, Category.assoc]
  have hi := congrArg (fun f => f.hom.left) e.inv_hom_id
  change e.inv.hom.left ≫ e.hom.hom.left = 𝟙 _ at hi
  rw [hi, Category.comp_id]

end AlgebraicGeometry.Scheme.FiniteEtale.Lifting
