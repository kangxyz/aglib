/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes
public import Aglib.AlgebraicGeometry.Descent.FiniteType.Separated

/-!
Separated finitely presented objects descend to separated actual models.
This uses base-change-family separatedness, not varying-source separatedness.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry.Scheme

/-- A separated finitely presented morphism has an actual separated model at
one stage of the supplied qcqs affine-transition limit. -/
theorem exists_separated_model_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [IsSeparated f] :
    ∃ (i : I) (M : FinitePresentationDescent.Model (c.π.app i) f),
      IsSeparated M.f := by
  obtain ⟨i, ⟨M⟩⟩ := exists_model_of_isLimit D c hc f
  have : CompactSpace M.X :=
    QuasiCompact.compactSpace_of_compactSpace (X := M.X) (Y := D.obj i) M.f
  have : QuasiSeparatedSpace M.X :=
    quasiSeparatedSpace_of_quasiSeparated (X := M.X) (Y := D.obj i) M.f
  have : IsSeparated (pullback.fst (c.π.app i) M.f) := by
    rw [← M.rawIso_inv_struct]
    infer_instance
  obtain ⟨j, hj⟩ := exists_isSeparated_pullback_fst_of_isLimit D c hc i M.f
  let : IsSeparated (pullback.fst (D.map j.hom) M.f) := hj
  refine ⟨j.left, M.rebase D c i j, ?_⟩
  change IsSeparated (pullback.snd M.f (D.map j.hom))
  rw [← pullbackSymmetry_hom_comp_fst M.f (D.map j.hom)]
  infer_instance

end AlgebraicGeometry.Scheme
