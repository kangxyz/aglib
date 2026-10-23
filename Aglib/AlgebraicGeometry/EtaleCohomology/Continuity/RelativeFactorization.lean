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
  let hV := representedSectionsCoconeIsColimit D c hc V
  obtain ⟨k, d, b, hdb⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hV).mp heq
  refine ⟨k.unop, b.unop, D.map d.unop ≫ r, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans hdb
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q ↦ q ≫ r) (c.w d.unop)).trans hr)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
