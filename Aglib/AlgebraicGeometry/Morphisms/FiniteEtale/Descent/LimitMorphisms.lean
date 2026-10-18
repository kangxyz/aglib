/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitClopen
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-!
# Descent of actual scheme morphisms to finite étale targets

The qcqs gluing input is the pinned Mathlib theorem
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` in
`AlgebraicGeometry/AffineTransitionLimit.lean`, revision
d13f23b723b8a846827a245b89c10fc7d3f11612. This file exposes its over-scheme
map and eventual-equality content for the FE-05 consumer. Finite étale object
descent is not assumed or concluded here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {S : Scheme.{u}}
  (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
  [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]

/-- The natural transformation consisting of the structural maps of the diagram objects over
`S`. -/
def overStructure : D ⋙ Over.forget S ⟶ (Functor.const I).obj S where
  app i := (D.obj i).hom
  naturality i j f := by simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hc in
/-- An actual morphism over `S` from a qcqs affine inverse limit to a locally
finitely presented `S`-scheme descends to an actual stage morphism over `S`. -/
theorem exists_overHom (Y : Over S) [LocallyOfFinitePresentation Y.hom]
    (q : c.pt ⟶ Y) : ∃ (i : I) (g : D.obj i ⟶ Y), c.π.app i ≫ g = q := by
  let E := D ⋙ Over.forget S
  let d := (Over.forget S).mapCone c
  have hlim : IsLimit d := isLimitOfPreserves (Over.forget S) hc
  have (i : I) : CompactSpace (E.obj i) := inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace (E.obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have {i j : I} (f : i ⟶ j) : IsAffineHom (E.map f) :=
    inferInstanceAs (IsAffineHom (D.map f).left)
  have hq : d.π ≫ overStructure D = (Functor.const I).map (q.left ≫ Y.hom) := by
    ext i
    exact (Over.w (c.π.app i)).trans (Over.w q).symm
  obtain ⟨i, g, hg, hgS⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      E (overStructure D) Y.hom d hlim q.left hq
  exact ⟨i, Over.homMk g hgS, Over.OverMorphism.ext hg⟩

include hc in
/-- Specialization to the repository's actual finite étale target category. -/
theorem exists_hom_to_cover (Y : Scheme.FiniteEtale S) (q : c.pt ⟶ Y.obj) :
    ∃ (i : I) (g : D.obj i ⟶ Y.obj), c.π.app i ≫ g = q :=
  exists_overHom D c hc Y.obj q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hc in
set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
/-- Two stage morphisms over `S` to a locally finite type scheme that agree
on the actual limit agree at a common later stage. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem overHom_eventually_eq (Y : Over S) [LocallyOfFiniteType Y.hom]
    {i j : I} (a : D.obj i ⟶ Y) (b : D.obj j ⟶ Y)
    (hab : c.π.app i ≫ a = c.π.app j ≫ b) :
    ∃ (k : I) (ki : k ⟶ i) (kj : k ⟶ j), D.map ki ≫ a = D.map kj ≫ b := by
  let E := D ⋙ Over.forget S
  let d := (Over.forget S).mapCone c
  have hlim : IsLimit d := isLimitOfPreserves (Over.forget S) hc
  have (i : I) : CompactSpace (E.obj i) := inferInstanceAs (CompactSpace (D.obj i).left)
  have {i j : I} (f : i ⟶ j) : IsAffineHom (E.map f) :=
    inferInstanceAs (IsAffineHom (D.map f).left)
  obtain ⟨k, ki, kj, h⟩ := Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
    E (overStructure D) Y.hom d hlim a.left (Over.w a).symm b.left (Over.w b).symm
    (congrArg (fun f ↦ f.left) hab)
  exact ⟨k, ki, kj, Over.OverMorphism.ext h⟩

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 25d5723f1f60fab340e45b582a99d3abc3cb6482612e2f910418de6bc888fe70.
Definitions, hypotheses and universes are retained modulo native names. -/
