/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.Basic
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.SmallCovers
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLift
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.TupleProducts
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CechReindex

/-! # Acyclicity of lifted small injectives

Small injectives give exact original tuple cochains. The actual tuple/product
comparison, arbitrary-product coefficient comparison and small-cover reindexing
transport that exactness to larger values. The basis criterion then proves
original cohomology acyclicity. Injective preservation is neither used nor claimed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

universe e c h w t

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasSheafify J AddCommGrpCat.{max c h w}]
  [HasSheafify J AddCommGrpCat.{max c h w t}]
  (B : CoverBasis.{c, h, max c w} J)

omit [HasSheafify J AddCommGrpCat.{max c h w t}] in
/-- Lifting a small injective gives Čech acyclicity on the original small
covers, viewed in the larger universe by actual index equivalences. -/
theorem cechAcyclic_valueLift_of_injective
    (F : Sheaf J AddCommGrpCat.{max c h w}) [Injective F] :
    CechAcyclic (CoverBasis.raise.{c, h, max c w, t} B)
      ((valueLift.{c, h, max c h w, t} J).obj F) := by
  intro W κ U hU n
  obtain ⟨ι, V, e, hV, rfl⟩ := hU
  have htuple := cechAcyclic_of_injective (B := B) F W ι V hV n
  have hproduct := htuple.of_iso (Presheaf.Cech.tupleHomCechIso.{c, h, w} V F.obj)
  have hlift :
      ((AddCommGrpCat.uliftFunctor.{t, max c h w}.mapHomologicalComplex _).obj
        ((cechComplexFunctor V).obj ((Over.forget W).op ⋙ F.obj))).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff]
    exact ((HomologicalComplex.exactAt_iff _ _).mp hproduct).map AddCommGrpCat.uliftFunctor
  have hcoeff := hlift.of_iso
    (CategoryTheory.Cech.cechComplexCoefficientIso AddCommGrpCat.uliftFunctor V
      ((Over.forget W).op ⋙ F.obj))
  have hreindex := hcoeff.of_iso
    (CategoryTheory.Cech.cechComplexReindexIso V e
      (((Over.forget W).op ⋙ F.obj) ⋙ AddCommGrpCat.uliftFunctor.{t})).symm
  exact hreindex.of_iso
    (Presheaf.Cech.tupleHomCechIso.{c, h, max w t} (V ∘ e)
      ((valueLift.{c, h, max c h w, t} J).obj F).obj).symm

variable [J.WEqualsLocallyBijective (Type (max c h w t))]
  [J.PreservesSheafification AddCommGrpCat.free.{max c h w t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h w t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max c h w t})]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max c h w t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h w t})]

/-- The larger-valued image of a small injective is acyclic for the original
`Sheaf.H`. This is the acyclicity needed for exact-functor Ext comparison. -/
theorem valueLift_injective_cohomology_subsingleton
    (F : Sheaf J AddCommGrpCat.{max c h w}) [Injective F]
    {T : C} (hT : IsTerminal T) (hBT : B.objects T) (n : ℕ) :
    Subsingleton (Sheaf.H.{e} ((valueLift.{c, h, max c h w, t} J).obj F) (n + 1)) :=
  subsingleton_of_forall_eq 0 fun x =>
    CechAcyclic.cohomology_eq_zero.{e, c, h, max c w t}
      (cechAcyclic_valueLift_of_injective.{c, h, w, t} B F) hT hBT n x

end CategoryTheory.Sheaf.BasisAcyclicity
