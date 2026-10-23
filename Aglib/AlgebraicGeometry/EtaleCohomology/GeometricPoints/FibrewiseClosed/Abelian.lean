/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FibrewiseClosed.Site
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-! # Fibrewise-closed geometric stalks detect isomorphisms of actual abelian sheaves -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed

universe u

variable {T S : Scheme.{u}} (p : T ⟶ S)

/-- The actual native abelian stalk at the selected algebraically closed geometric point,
with the point and coefficient functors both valued in universe `u + 1`. -/
def geometricStalk (x : Index p) :
    AbelianSheaf.{u, u + 1} T ⥤ AddCommGrpCat.{u + 1} :=
  (largePoint (geometricPoint x.val)).sheafFiber

variable [LocallyOfFiniteType p]

/-- The native point-family interface jointly reflects isomorphisms on the
actual standard-universe abelian sheaf category. -/
theorem jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms (fun Φ : (pointFamily p).FullSubcategory =>
      Φ.obj.sheafFiber (A := AddCommGrpCat.{u + 1})) :=
  (pointFamily_isConservative p).jointlyReflectIsomorphisms AddCommGrpCat.{u + 1}

/-- An actual abelian-sheaf morphism is an isomorphism if its original maps
on all fibrewise-closed geometric stalks are isomorphisms. -/
theorem isIso_of_geometricStalks
    {F G : AbelianSheaf.{u, u + 1} T} (f : F ⟶ G)
    (h : ∀ x : Index p, IsIso ((geometricStalk p x).map f)) : IsIso f := by
  rw [(jointlyReflectIsomorphisms p).isIso_iff]
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x⟩ := hΦ
  exact h x

/-- Testing all actual algebraically closed geometric points closed in their
fibres suffices for the original morphism of standard-universe abelian sheaves. -/
theorem isIso_of_all_fibrewiseClosed_geometricStalks
    {F G : AbelianSheaf.{u, u + 1} T} (f : F ⟶ G)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ T),
      IsFibrewiseClosed p (η default) →
        IsIso ((largePoint η).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.map f)) :
    IsIso f := by
  apply isIso_of_geometricStalks p f
  intro x
  apply h (pointField x.val) (geometricPoint x.val)
  simpa only [geometricPoint_apply] using x.property

end AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed
