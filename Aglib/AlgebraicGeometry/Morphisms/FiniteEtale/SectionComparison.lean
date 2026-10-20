/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointComparison
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ResidueFiber
public import Aglib.AlgebraicGeometry.FundamentalGroup.SectionLifting

/-!
# The original residue point of the actual lifted section

The section is exactly the existing `henselianPointAboveSection`. Its stated
restriction equation, followed by the supplied actual comparison, recovers
the original chosen residue point. The universal proper-Henselian comparison
remains an explicit input; neither its existence nor a new section constructor
is asserted here.

Source: `OneGonLift:188` and `GeneralLift:151` in
`R5Lab.AlgebraicGeometry.Curves.LocalModels.CyclicCovers`, R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256 respectively
`e26ed93e094ea09b9e080a7b913bd0dc919b073c13f03654768a1c687dd5aca3` and
`e62cfc4cb7711bac753202a8bcf27fbf4f11a52cf87ccf144ffb6df9b5671075`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.Lifting

universe u
variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {Y : Scheme.{u}}

/-- The same section construction and the same comparison preserve the
supplied residue point as an actual scheme morphism. -/
theorem henselianPointAboveSection_compare (H : ProperHenselianComparison R)
    (π : Y ⟶ Spec (.of R)) (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ π = 𝟙 _)
    (C : FiniteEtale Y) (C₀ : FiniteEtale (LocalRing.ResidueFiber.obj π))
    (e : (baseChange (LocalRing.ResidueFiber.projection π)).obj C ≅ C₀)
    (s : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C₀.obj.left)
    (hs : s ≫ C₀.obj.hom = LocalRing.ResidueFiber.section π σ hσ) :
    let t : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C.obj.left :=
      s ≫ e.inv.hom.left ≫
      pullback.fst C.obj.hom (LocalRing.ResidueFiber.projection π)
    let ht : t ≫ C.obj.hom = LocalRing.residueSpecMap R ≫ σ := by
      dsimp only [t]
      rw [comparisonPoint_over, hs, LocalRing.ResidueFiber.section_projection]
    let a : Spec (.of R) ⟶ C.obj.left :=
      SectionLifting.henselianPointAboveSection R H C σ t ht
    pullback.lift (f := C.obj.hom) (g := LocalRing.ResidueFiber.projection π)
      (LocalRing.residueSpecMap R ≫ a)
        (LocalRing.ResidueFiber.section π σ hσ) (by
          exact (Category.assoc _ _ _).trans
            ((congrArg (fun q : Spec (.of R) ⟶ Y => LocalRing.residueSpecMap R ≫ q)
              (SectionLifting.henselianPointAboveSection_over R H C σ t ht)).trans
                (LocalRing.ResidueFiber.section_projection π σ hσ).symm)) ≫
      e.hom.hom.left = s := by
  dsimp only
  have hw := Over.w e.inv.hom
  change e.inv.hom.left ≫
    pullback.snd C.obj.hom (LocalRing.ResidueFiber.projection π) = C₀.obj.hom at hw
  calc
    _ = (s ≫ e.inv.hom.left) ≫ e.hom.hom.left := by
      congr 1
      apply pullback.hom_ext (f := C.obj.hom)
        (g := LocalRing.ResidueFiber.projection π)
      · simpa only [pullback.lift_fst, Category.assoc, LocalRing.residueSpecMap] using
          SectionLifting.henselianPointAboveSection_restrict R H C σ
            (s ≫ e.inv.hom.left ≫
              pullback.fst C.obj.hom (LocalRing.ResidueFiber.projection π))
            (by rw [comparisonPoint_over, hs, LocalRing.ResidueFiber.section_projection])
      · simpa only [pullback.lift_snd, Category.assoc, hw] using hs.symm
    _ = s := by
      have hi := congrArg (fun f => f.hom.left) e.inv_hom_id
      change e.inv.hom.left ≫ e.hom.hom.left = 𝟙 _ at hi
      rw [Category.assoc, hi, Category.comp_id]

end AlgebraicGeometry.Scheme.FiniteEtale.Lifting
