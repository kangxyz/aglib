/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Sites.Canonical

/-!
# Global sections on subcanonical scheme sites

The original commutative-ring-valued global-sections functor is a sheaf for
any subcanonical topology on schemes. Its underlying presheaf of sets is
represented by the spectrum of the free commutative ring on one generator.
The statements retain the scheme universe and do not assume large limits in
the category of small commutative rings.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

universe u

private def sectionsHomRepresentableBy (A : CommRingCat.{u}) :
    (Scheme.Γ ⋙ coyoneda.obj (op A)).RepresentableBy (Scheme.Spec.obj (op A)) where
  homEquiv {X} :=
    ((ΓSpec.adjunction.homEquiv X (op A)).symm).trans (CategoryTheory.opEquiv _ _)
  homEquiv_comp f g := by
    change ((ΓSpec.adjunction.homEquiv _ (op A)).symm (f ≫ g)).unop =
      ((ΓSpec.adjunction.homEquiv _ (op A)).symm g).unop ≫ Scheme.Γ.map f.op
    rw [ΓSpec.adjunction.homEquiv_naturality_left_symm]
    rfl

/-- The original ring of global sections is a sheaf for every subcanonical
Grothendieck topology on schemes. -/
theorem globalSections_isSheaf (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] :
    Presheaf.IsSheaf J Scheme.Γ := by
  intro A
  let := (sectionsHomRepresentableBy A).isRepresentable
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

private abbrev sectionsCoordinateRing : CommRingCat.{u} :=
  CommRingCat.free.obj PUnit.{u + 1}

private def sectionsUnderlyingRepresentableBy :
    (Scheme.Γ ⋙ CategoryTheory.forget CommRingCat.{u}).RepresentableBy
      (Scheme.Spec.obj (op sectionsCoordinateRing)) where
  homEquiv {X} :=
    ((sectionsHomRepresentableBy sectionsCoordinateRing).homEquiv.trans
      (CommRingCat.adj.homEquiv PUnit.{u + 1} (Scheme.Γ.obj (op X)))).trans
        (TypeCat.homEquiv.trans (Equiv.funUnique _ _))
  homEquiv_comp f g := by
    change (CommRingCat.adj.homEquiv _ _
      ((sectionsHomRepresentableBy sectionsCoordinateRing).homEquiv (f ≫ g))) PUnit.unit = _
    rw [Functor.RepresentableBy.homEquiv_comp]
    change (CommRingCat.adj.homEquiv _ _
      ((sectionsHomRepresentableBy sectionsCoordinateRing).homEquiv g ≫
        Scheme.Γ.map f.op)) PUnit.unit = _
    rw [CommRingCat.adj.homEquiv_naturality_right]
    rfl

/-- The underlying presheaf of original global sections is representable. -/
instance globalSectionsUnderlying_isRepresentable :
    (Scheme.Γ ⋙ CategoryTheory.forget CommRingCat.{u}).IsRepresentable :=
  sectionsUnderlyingRepresentableBy.isRepresentable

/-- The underlying small set of original global sections is a sheaf without
increasing the coefficient universe. -/
theorem globalSectionsUnderlying_isSheaf (J : GrothendieckTopology Scheme.{u})
    [J.Subcanonical] : Presieve.IsSheaf J (Scheme.Γ ⋙ CategoryTheory.forget CommRingCat.{u}) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

end AlgebraicGeometry.Scheme
