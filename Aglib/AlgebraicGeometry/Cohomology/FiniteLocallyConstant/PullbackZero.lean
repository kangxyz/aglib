/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Basic
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.PullbackComposition

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant.PullbackZero` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`069bf5c728982c3b10c430a153055447c3caba7327fc92f590688c4b285ef748`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.EtaleH1 _root_.CategoryTheory.Functor.LargePresheaf
namespace AlgebraicGeometry.Scheme.EtaleH1.PullbackZero
universe u wX wC wK
section PullbackZero
variable {X Y Z : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wC} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{wK} (AbelianSheaf.{u, u + 1} Z)]

theorem composite_pullback_zero_iff (f : Y ⟶ X) (g : Z ⟶ Y)
    (L : AbelianSheaf.{u, u + 1} X) (a : H1Etale X L) :
    h1Pullback (g ≫ f) L a = 0 ↔
      h1Pullback g ((inverseImage f).obj L) (h1Pullback f L a) = 0 := by
  let E := coefficientIso.{u, u + 1, wK} ((inverseImageComp f g).app L)
  have h : E (h1Pullback (g ≫ f) L a) =
      h1Pullback g ((inverseImage f).obj L) (h1Pullback f L a) := h1Pullback_comp f g L a
  constructor
  · intro hz
    exact h.symm.trans ((congrArg E hz).trans (map_zero E))
  · intro hz
    exact E.injective ((h.trans hz).trans (map_zero E).symm)

theorem coefficient_iso_pullback_zero_iff (f : Y ⟶ X)
    {L N : AbelianSheaf.{u, u + 1} X} (e : L ≅ N) (a : H1Etale X L) :
    h1Pullback f N (coefficientMap e.hom a) = 0 ↔ h1Pullback f L a = 0 := by
  let E := coefficientIso.{u, u + 1, wC} ((inverseImage f).mapIso e)
  have h : h1Pullback f N (coefficientMap e.hom a) = E (h1Pullback f L a) :=
    h1Pullback_coefficientMap f e.hom a
  constructor
  · intro hz
    exact E.injective ((h.symm.trans hz).trans (map_zero E).symm)
  · intro hz
    exact h.trans ((congrArg E hz).trans (map_zero E))

end PullbackZero
end AlgebraicGeometry.Scheme.EtaleH1.PullbackZero
