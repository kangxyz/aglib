/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.GraphClosure
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Base-change comparisons and section lifts for the actual graph closure

The original graph closure becomes the original source over a base change
whose source pullback is the chosen open. A specified isomorphism of the
two base changes gives the comparison with the target as well. Both
comparisons retain the actual graph projections. Scheme-theoretic density
gives an actual closed-immersion factorization of compatible section data.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.GraphClosure

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens)
  (h : U.toScheme ⟶ Y) (w : U.ι ≫ f = h ≫ g)

/-- The original source projection as an arrow over the original base. -/
def overSource : Over.mk (toSource f g U h w ≫ f) ⟶ Over.mk f :=
  Over.homMk (toSource f g U h w) rfl

/-- The original target projection as an arrow over the original base. -/
def overTarget : Over.mk (toSource f g U h w ≫ f) ⟶ Over.mk g :=
  Over.homMk (toTarget f g U h w) (toSource_comp f g U h w).symm

/-- The original open graph is exactly the inverse image of its source open. -/
lemma isPullback_fromOpen [IsProper g] [QuasiCompact U.ι] :
    IsPullback (fromOpen f g U h w) (𝟙 U.toScheme) (toSource f g U h w) U.ι := by
  let E := (toSourceRestrictIso f g U h w).symm
  refine (isPullback_morphismRestrict (toSource f g U h w) U).flip.of_iso'
    E (.refl _) (.refl _) (.refl _) ?_ ?_ ?_ ?_
  · simp [E, toSourceRestrictIso_inv]
  · simp [E, toSourceRestrictIso_inv]
  · simp
  · simp

variable {T : Scheme.{u}} (j : T ⟶ S) (k : U.toScheme ⟶ T)
  (H : IsPullback U.ι k f j)

include H

/-- A cartesian source-open comparison gives the cartesian comparison
between the original open graph and the original base change of its closure. -/
lemma isPullback_fromOpen_toBase [IsProper g] [QuasiCompact U.ι] :
    IsPullback (fromOpen f g U h w) k (toSource f g U h w ≫ f) j := by
  simpa only [Category.id_comp] using (isPullback_fromOpen f g U h w).paste_vert H

/-- The literal base change of the graph closure identified with the
literal base change of the source. -/
def baseChangeSourceIso [IsProper g] [QuasiCompact U.ι] :
    (Over.pullback j).obj (Over.mk (toSource f g U h w ≫ f)) ≅
      (Over.pullback j).obj (Over.mk f) :=
  Over.isoMk
    ((isPullback_fromOpen_toBase f g U h w j k H).isoPullback.symm ≪≫ H.isoPullback)
    (by simp)

/-- The forward comparison is the base change of the original projection. -/
lemma baseChangeSourceIso_hom [IsProper g] [QuasiCompact U.ι] :
    (baseChangeSourceIso f g U h w j k H).hom = (Over.pullback j).map (overSource f g U h w) := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (isPullback_fromOpen_toBase f g U h w j k H).isoPullback.hom).mp
  apply pullback.hom_ext (f := f) (g := j) <;>
    simp [baseChangeSourceIso, overSource, Over.pullback_map_left, Category.assoc]

/-- The actual source projection becomes an isomorphism after the given
base change. -/
lemma isIso_baseChange_overSource [IsProper g] [QuasiCompact U.ι] :
    IsIso ((Over.pullback j).map (overSource f g U h w)) := by
  rw [← baseChangeSourceIso_hom f g U h w j k H]
  infer_instance

/-- A specified isomorphism between the original literal base changes is
exactly the relation between the two actual graph projections after base change. -/
lemma baseChange_overTarget_eq [IsProper g] [QuasiCompact U.ι]
    (e : (Over.pullback j).obj (Over.mk f) ≅ (Over.pullback j).obj (Over.mk g))
    (he : h = H.isoPullback.hom ≫ e.hom.left ≫ pullback.fst g j) :
    (Over.pullback j).map (overTarget f g U h w) =
      (baseChangeSourceIso f g U h w j k H).hom ≫ e.hom := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (isPullback_fromOpen_toBase f g U h w j k H).isoPullback.hom).mp
  apply pullback.hom_ext (f := g) (g := j)
  · simpa [baseChangeSourceIso, overTarget, Over.pullback_map_left, Category.assoc] using he
  · have ew : e.hom.left ≫ pullback.snd g j = pullback.snd f j := Over.w e.hom
    simp [baseChangeSourceIso, Over.pullback_map_left, Category.assoc, ew]

/-- The target comparison retains both the original projection and the
specified isomorphism of the original base changes. -/
lemma isIso_baseChange_overTarget [IsProper g] [QuasiCompact U.ι]
    (e : (Over.pullback j).obj (Over.mk f) ≅ (Over.pullback j).obj (Over.mk g))
    (he : h = H.isoPullback.hom ≫ e.hom.left ≫ pullback.fst g j) :
    IsIso ((Over.pullback j).map (overTarget f g U h w)) := by
  rw [baseChange_overTarget_eq f g U h w j k H e he]
  infer_instance

omit H k in
/-- Scheme-theoretic density promotes a factorization on the actual
base change to kernel containment for the whole supplied morphism. -/
lemma image_kernel_le_of_dense [IsSchemeTheoreticallyDominant j]
    (δ : S ⟶ pullback f g) (σ : T ⟶ U.toScheme)
    (hσ : σ ≫ graph f g U h w = j ≫ δ) :
    (graph f g U h w).imageι.ker ≤ δ.ker := by
  calc
    (graph f g U h w).imageι.ker = (graph f g U h w).ker := by
      simp only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
    _ ≤ (σ ≫ graph f g U h w).ker := σ.le_ker_comp _
    _ = (j ≫ δ).ker := congrArg Scheme.Hom.ker hσ
    _ = δ.ker := by rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]

omit H k in
/-- The actual lift to the original closed graph image, obtained from
kernel containment rather than set-theoretic containment. -/
def liftFromDense [IsSchemeTheoreticallyDominant j]
    (δ : S ⟶ pullback f g) (σ : T ⟶ U.toScheme)
    (hσ : σ ≫ graph f g U h w = j ≫ δ) : S ⟶ closure f g U h w :=
  IsClosedImmersion.lift (graph f g U h w).imageι δ
    (image_kernel_le_of_dense f g U h w j δ σ hσ)

omit H k in
/-- The lifted morphism has exactly the original map into the fibre product. -/
@[reassoc (attr := simp)]
lemma liftFromDense_inclusion [IsSchemeTheoreticallyDominant j]
    (δ : S ⟶ pullback f g) (σ : T ⟶ U.toScheme)
    (hσ : σ ≫ graph f g U h w = j ≫ δ) :
    liftFromDense f g U h w j δ σ hσ ≫ (graph f g U h w).imageι = δ :=
  IsClosedImmersion.lift_fac _ _ _

omit H k in
/-- The source triangle for the actual lift to the graph closure. -/
@[reassoc (attr := simp)]
lemma liftFromDense_toSource [IsSchemeTheoreticallyDominant j]
    (δ : S ⟶ pullback f g) (σ : T ⟶ U.toScheme)
    (hσ : σ ≫ graph f g U h w = j ≫ δ) :
    liftFromDense f g U h w j δ σ hσ ≫ toSource f g U h w = δ ≫ pullback.fst f g := by
  simp [toSource, ← Category.assoc]

omit H k in
/-- The target triangle for the actual lift to the graph closure. -/
@[reassoc (attr := simp)]
lemma liftFromDense_toTarget [IsSchemeTheoreticallyDominant j]
    (δ : S ⟶ pullback f g) (σ : T ⟶ U.toScheme)
    (hσ : σ ≫ graph f g U h w = j ≫ δ) :
    liftFromDense f g U h w j δ σ hσ ≫ toTarget f g U h w = δ ≫ pullback.snd f g := by
  simp [toTarget, ← Category.assoc]

end AlgebraicGeometry.Scheme.GraphClosure
