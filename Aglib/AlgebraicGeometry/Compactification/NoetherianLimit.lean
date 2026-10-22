/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Noetherian
public import Aglib.AlgebraicGeometry.Compactification.BaseChange
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.SeparatedModels

/-!
Compactification of a separated finitely presented morphism over a supplied
actual affine-transition limit of Noetherian schemes. The original base and
morphism are retained; the limit is not assumed Noetherian.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Descend the actual separated fp object, compactify over the Noetherian
stage, and base change its compactification to the original morphism. -/
theorem exists_compactification_of_noetherian_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    [∀ i, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [IsSeparated f] :
    Nonempty f.Compactification := by
  have (i : I) : CompactSpace (D.obj i) := inferInstance
  have (i : I) : QuasiSeparatedSpace (D.obj i) := inferInstance
  obtain ⟨i, M, hM⟩ := Scheme.exists_separated_model_of_isLimit D c hc f
  let : IsSeparated M.f := hM
  obtain ⟨C⟩ := M.f.exists_compactification_of_isNoetherian
  exact ⟨(C.baseChange (c.π.app i)).ofSourceIso f M.rawIso M.rawIso_hom_fst⟩

end AlgebraicGeometry.Scheme.Hom
