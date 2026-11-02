/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimitSections

/-!
# Relative factorizations descend along affine-transition limits

Finite-presentation descent first produces a map at a stage. Eventual equality
then enforces its triangle over a second locally finitely presented target.
The source stages need not be finitely presented over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {X : Scheme.{u}}
  (D : I ⥤ Over X) (c : Cone D)
  (hc : IsLimit ((Over.forget X).mapCone c))
  [∀ i, CompactSpace (D.obj i).left]
  [∀ i, QuasiSeparatedSpace (D.obj i).left]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).left]

include hc in
/-- Descend an actual relative factorization while preserving both triangles. -/
theorem exists_relative_factorization {U V : Over X}
    [LocallyOfFinitePresentation U.hom] [LocallyOfFinitePresentation V.hom]
    (i : I) (a : D.obj i ⟶ V) (v : U ⟶ V) (s : c.pt ⟶ U)
    (hs : s ≫ v = c.π.app i ≫ a) :
    ∃ (k : I) (b : k ⟶ i) (r : D.obj k ⟶ U),
      r ≫ v = D.map b ≫ a ∧ c.π.app k ≫ r = s := by
  let hU := representedSectionsCoconeIsColimit D c hc U
  obtain ⟨j, r, hr⟩ := Types.jointly_surjective_of_isColimit hU s
  have heq : c.π.app j.unop ≫ (r ≫ v) = c.π.app i ≫ a :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q ↦ q ≫ v) hr).trans hs)
  let D₀ := D ⋙ Over.forget X
  have (j : I) : CompactSpace (D₀.obj j) :=
    inferInstanceAs (CompactSpace (D.obj j).left)
  have (j : I) : QuasiSeparatedSpace (D₀.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j).left)
  have {j k : I} (f : j ⟶ k) : IsAffineHom (D₀.map f) :=
    inferInstanceAs (IsAffineHom (D.map f).left)
  let t : D₀ ⟶ (Functor.const I).obj X := {
    app j := (D.obj j).hom
    naturality {j k} f := by
      change (D.map f).left ≫ (D.obj k).hom = (D.obj j).hom ≫ 𝟙 X
      rw [Category.comp_id]
      exact Over.w (D.map f) }
  obtain ⟨k, d, b, hdb⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType D₀ t V.hom
      ((Over.forget X).mapCone c) hc
      (r ≫ v).left (Over.w (r ≫ v)).symm a.left (Over.w a).symm
      (congrArg (fun q => q.left) heq)
  have hdb' : D.map d ≫ (r ≫ v) = D.map b ≫ a :=
    Over.OverMorphism.ext hdb
  refine ⟨k, b, D.map d ≫ r, (Category.assoc _ _ _).trans hdb', ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ r) (c.w d)).trans hr)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
