/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GeneratorModels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstructibleFinitePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleFiniteOpenCover

/-! # Original coefficient models over arbitrary finite affine covers

Every affine-etale generator is assembled from the inverse images of a finite
affine cover of an original stage. Its intersections stay affine in the
unchanged affine source. Binary generator pushouts glue the actual finite
family; the existing finite-diagram engine supplies its original stage model.
This removes the two-chart restriction, without choosing another limit model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
namespace ModelDescent

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

open Constructible.Modules.NativeFreePresentation

variable (R : Type (u + 1)) [Ring R]

/-- The original free generator on an affine open lying in one specified
model chart has an actual canonical stage model. -/
theorem free_openChart_hasStageModel
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (V : (D.obj i).Opens) (hV : IsAffineOpen V)
    (U : c.pt.Etale) (W : U.left.Opens) (hW : IsAffineOpen W)
    (hWV : W ≤ (U.hom ≫ c.π.app i) ⁻¹ᵁ V) :
    HasStageModel D.op c.op R
      (free R c.pt (Constructible.PositivePresentation.FiniteOpenCover.openChart U W)) := by
  let : IsAffine V.toScheme := hV
  let : Etale U.hom := U.prop
  let A := Constructible.PositivePresentation.FiniteOpenCover.openChart U W
  have : IsAffine A.left := hW
  let t := U.hom ≫ c.π.app i
  let f : A.left ⟶ pullback (c.π.app i) V.ι :=
    pullback.lift (W.ι ≫ U.hom) (t.resLE V W hWV)
      ((Category.assoc W.ι U.hom (c.π.app i)).trans
        (Scheme.Hom.resLE_comp_ι t hWV).symm)
  have hf : f ≫ pullback.fst (c.π.app i) V.ι = A.hom := pullback.lift_fst _ _ _
  have : Etale (f ≫ pullback.fst (c.π.app i) V.ι) := by
    rw [hf]
    exact A.prop
  let : Etale f := Etale.of_comp f (pullback.fst (c.π.app i) V.ι)
  exact free_hasStageModel_of_chart_factorization R D c hc i V.ι A f hf


/-- An original affine generator over any finite affine stage cover has an
actual native module stage model with its original inverse-image isomorphism. -/
theorem free_hasStageModel_of_finiteCharts
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (V : Finset (D.obj i).affineOpens) (hcover : V.sup (fun W => W.1) = ⊤)
    (U : c.pt.Etale) [IsAffine U.left] [IsAffineHom U.hom] :
    HasStageModel D.op c.op R (free R c.pt U) := by
  classical
  let : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  let t := U.hom ≫ c.π.app i
  have : IsAffineHom t := inferInstance
  let P := HasStageModel D.op c.op R
  have {k l : Iᵒᵖ} (q : k ⟶ l) : IsAffineHom (D.op.map q).unop :=
    inferInstanceAs (IsAffineHom (D.map q.unop))
  let : P.IsClosedUnderFiniteColimits :=
    hasStageModel_closedFiniteColimits R D.op c.op hc.op
  let B := fun W : U.left.Opens => IsAffineOpen W ∧
    ∃ Z : (D.obj i).affineOpens, W ≤ t ⁻¹ᵁ Z.1
  have hB (W Z : U.left.Opens) (hW : B W) (hZ : B Z) : B (W ⊓ Z) := by
    refine ⟨hW.1.inf hZ.1, ?_⟩
    obtain ⟨A, hA⟩ := hW.2
    exact ⟨A, inf_le_left.trans hA⟩
  have hP (W : U.left.Opens) (hW : B W) :
      P (free R c.pt (Constructible.PositivePresentation.FiniteOpenCover.openChart U W)) := by
    obtain ⟨Z, hZ⟩ := hW.2
    exact free_openChart_hasStageModel R D c hc i Z.1 Z.2 U W hW.1 hZ
  have hbot : P (free R c.pt (Constructible.PositivePresentation.FiniteOpenCover.openChart U ⊥)) :=
    free_openChart_hasStageModel R D c hc i ⊥ (isAffineOpen_bot _)
      U ⊥ (isAffineOpen_bot _) bot_le
  let s := V.image (fun W => t ⁻¹ᵁ W.1)
  have hs : ∀ W ∈ s, B W := by
    intro W hW
    obtain ⟨Z, _, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨Z.2.preimage t, Z, le_rfl⟩
  have hpre (A : Finset (D.obj i).affineOpens) :
      A.sup (fun W => t ⁻¹ᵁ W.1) = t ⁻¹ᵁ A.sup (fun W => W.1) := by
    induction A using Finset.induction_on with
    | empty => simp only [Finset.sup_empty, Scheme.Hom.preimage_bot]
    | insert W A hWA ih =>
      simp only [Finset.sup_insert, Scheme.Hom.preimage_sup, ih]
  have htop : s.sup id = ⊤ := by
    rw [show s.sup id = V.sup (fun W => t ⁻¹ᵁ W.1) by
      simp only [s, Finset.sup_image, Function.comp_def, id_eq]]
    rw [hpre, hcover, Scheme.Hom.preimage_top]
  exact FiniteOpenCover.prop_free_of_finiteCover R U P B hB hP hbot s hs htop

/-- Quasi-compactness of one actual stage supplies its finite affine cover
internally. No two-chart hypothesis is required. -/
theorem free_hasStageModel_of_compactStage
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I) [CompactSpace (D.obj i)]
    (U : c.pt.Etale) [IsAffine U.left] [IsAffineHom U.hom] :
    HasStageModel D.op c.op R (free R c.pt U) := by
  classical
  obtain ⟨s, hs, he⟩ :=
    isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (show IsCompact ((⊤ : (D.obj i).Opens) : Set (D.obj i)) from isCompact_univ)
  apply free_hasStageModel_of_finiteCharts R D c hc i hs.toFinset ?_ U
  rw [Finset.sup_eq_iSup]
  simpa only [Set.Finite.mem_toFinset] using he.symm

/-- Actual constructible native module coefficients on a quasi-compact separated
limit descend to native finite-colimit stages over the original diagram. -/
theorem constructible_hasStageModel_of_compactStage [IsNoetherianRing R]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) [CompactSpace c.pt] [c.pt.IsSeparated]
    (i : I) [CompactSpace (D.obj i)]
    (F : Coefficient R c.pt) (hF : Constructible.Modules.IsConstructible F) :
    HasStageModel D.op c.op R F := by
  have {k l : Iᵒᵖ} (q : k ⟶ l) : IsAffineHom (D.op.map q).unop :=
    inferInstanceAs (IsAffineHom (D.map q.unop))
  let : IsSeparated (terminal.from c.pt) :=
    (inferInstance : c.pt.IsSeparated).isSeparated_terminal_from
  apply finiteColimitStage_hasStageModel D.op c.op R hc.op ?_ F
    (Constructible.Modules.finiteColimitStage_of_isConstructible R F hF)
  intro U
  let W := (Scheme.AffineEtale.Spec c.pt).obj U
  have : IsAffine W.left := inferInstanceAs (IsAffine (Spec U.left.unop))
  have ht : W.hom ≫ terminal.from c.pt = terminal.from W.left := terminal.comp_from _
  have hterminal : IsAffineHom (terminal.from W.left) := inferInstance
  have hcomp : IsAffineHom (W.hom ≫ terminal.from c.pt) := ht.symm ▸ hterminal
  let : IsAffineHom W.hom := @IsAffineHom.of_comp W.left c.pt (⊤_ Scheme.{u})
    W.hom (terminal.from c.pt) hcomp inferInstance
  exact free_hasStageModel_of_compactStage R D c hc i W

end ModelDescent
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
