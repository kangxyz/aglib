/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing

/-! # Complete original Hom-section gluing before native specialization -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u v

variable {X : Scheme.{u}} {ι : Type v}
  (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
  (M N : X.Modules) (f : ∀ i, M.restrict (a i) ⟶ N.restrict (a i))

/-- The original local arrows, as a whole family of original Hom sections. -/
def restrictionHomSections (i : ι) : Γ(sheaf X M N, (a i).opensRange) :=
  restrictionHomEquiv (a i) M N (f i)

/-- Native overlap compatibility supplies the whole matching-section law. -/
theorem restrictionHomSections_compatible (hcomp : RestrictionHomCompatible a M N f) :
    TopCat.Presheaf.IsCompatible (sheaf X M N).val.presheaf
      (fun i => (a i).opensRange) (restrictionHomSections Y a M N f) := by
  intro i k
  exact restrictionHomSections_overlap (a i) (a k) M N (f i) (f k) (hcomp i k)

variable (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
  (hcomp : RestrictionHomCompatible a M N f)

/-- The original unique sheaf-gluing choice, made before geometric substitution. -/
def gluedRestrictionHomSection : Γ(sheaf X M N, (⊤ : X.Opens)) := by
  let H := sheaf X M N
  let A : TopCat.Sheaf Ab X := ⟨H.val.presheaf, H.isSheaf⟩
  exact (A.existsUnique_gluing' (fun i => (a i).opensRange) ⊤
    (fun _ => homOfLE le_top) (restrictionRanges_cover Y a hcover).ge
    (restrictionHomSections Y a M N f)
    (restrictionHomSections_compatible Y a M N f hcomp)).choose

/-- The chosen original section restricts to each supplied native local arrow. -/
theorem gluedRestrictionHomSection_restrict (i : ι) :
    (sheaf X M N).val.map (homOfLE (show (a i).opensRange ≤ ⊤ from le_top)).op
      (gluedRestrictionHomSection Y a M N f hcover hcomp) =
        restrictionHomSections Y a M N f i := by
  let H := sheaf X M N
  let A : TopCat.Sheaf Ab X := ⟨H.val.presheaf, H.isSheaf⟩
  exact (A.existsUnique_gluing' (fun i => (a i).opensRange) ⊤
    (fun _ => homOfLE le_top) (restrictionRanges_cover Y a hcover).ge
    (restrictionHomSections Y a M N f)
    (restrictionHomSections_compatible Y a M N f hcomp)).choose_spec.1 i

end AlgebraicGeometry.Scheme.Modules.InternalHom
