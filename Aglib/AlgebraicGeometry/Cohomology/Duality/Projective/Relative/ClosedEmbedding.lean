/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.Exact
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition

/-!
# Original relative Serre maps through a chosen closed embedding

The installed closed right adjoint and original pushforward-composition map
transfer the literal ambient comparison. Its forward formula retains every
supplied injective resolution and the original adjunction. The transfer
preserves bijectivity exactly; this construction does not supply the pending
ambient coherent duality theorem or a canonical-bundle identification.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Y)

/-- The original geometric composition followed by the original exact closed-image single. -/
def relativeClosedEmbeddingPushforwardSingleIso (M : Z.Modules) :
    (Scheme.Modules.derivedPushforwardPlus (i ≫ p)).obj
        ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M) ≅
      (Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((Scheme.Modules.pushforward i).obj M)) :=
  (Scheme.Modules.derivedPushforwardPlusCompIso i p).app
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M) ≪≫
    (Scheme.Modules.derivedPushforwardPlus p).mapIso
      (((Scheme.Modules.pushforward i).rightDerivedFunctorPlusSingleIso 0).app M)

/-- The original geometric single comparison is natural for every native Ext class,
with the installed composition and exact-single shift comparisons. -/
@[reassoc]
theorem relativeClosedEmbeddingPushforwardSingleIso_ext_naturality
    {M M' : Z.Modules} {r : ℕ} (α : Ext.{u + 1} M M' r) :
    DerivedCategory.Plus.ι.map (relativeClosedEmbeddingPushforwardSingleIso i p M).hom ≫
        (α.mapExactFunctor (Scheme.Modules.pushforward i)).homPlus.map
          (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι) =
      α.homPlus.map
          (Scheme.Modules.derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι) ≫
        (DerivedCategory.Plus.ι.map
          (relativeClosedEmbeddingPushforwardSingleIso i p M').hom)⟦(r : ℤ)⟧' := by
  let F := Scheme.Modules.pushforward i
  let Ri := Scheme.Modules.derivedPushforwardPlus i
  let P := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  let s := F.rightDerivedFunctorPlusSingleIso 0
  let compIso := Scheme.Modules.derivedPushforwardPlusCompIso i p
  let L : Scheme.Modules.derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι ≅
      Ri ⋙ P :=
    Functor.isoWhiskerRight compIso DerivedCategory.Plus.ι ≪≫
      Functor.associator Ri (Scheme.Modules.derivedPushforwardPlus p) DerivedCategory.Plus.ι
  let : NatTrans.CommShift L.hom ℤ := by
    dsimp [L]
    infer_instance
  have hL (T : DerivedCategory.Plus Z.Modules) :
      L.hom.app T = DerivedCategory.Plus.ι.map (compIso.hom.app T) := by
    change DerivedCategory.Plus.ι.map (compIso.hom.app T) ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hcomp :
      α.homPlus.map
          (Scheme.Modules.derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι) ≫
          (DerivedCategory.Plus.ι.map (compIso.hom.app
            ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M')))⟦(r : ℤ)⟧' =
        DerivedCategory.Plus.ι.map (compIso.hom.app
            ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)) ≫
          (α.homPlus.map Ri).map P := by
    have hn := ShiftedHom.map_naturality α.homPlus L.hom
    rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, hL, hL] at hn
    simpa only [ShiftedHom.comp_map] using hn
  have hs₀ : s.inv.app M ≫ α.homPlus.map Ri ≫ (s.hom.app M')⟦(r : ℤ)⟧' =
      (α.mapExactFunctor F).homPlus :=
    F.rightDerivedFunctorPlusSingleIso_map_homPlus α
  have hs :
      (ShiftedHom.mk₀ (0 : ℤ) rfl (s.hom.app M)).comp
          (α.mapExactFunctor F).homPlus (add_zero _) =
        (α.homPlus.map Ri).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (s.hom.app M')) (zero_add _) := by
    rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ← hs₀]
    simp only [Iso.hom_inv_id_app_assoc]
  have hs' := congrArg (fun z => ShiftedHom.map z P) hs
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at hs'
  simp only [relativeClosedEmbeddingPushforwardSingleIso, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  change DerivedCategory.Plus.ι.map (compIso.hom.app
      ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)) ≫
      P.map (s.hom.app M) ≫ (α.mapExactFunctor F).homPlus.map P =
    α.homPlus.map
        (Scheme.Modules.derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι) ≫
      (DerivedCategory.Plus.ι.map (compIso.hom.app
        ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M')))⟦(r : ℤ)⟧' ≫
      (P.map (s.hom.app M'))⟦(r : ℤ)⟧'
  rw [hs', ← reassoc_of% hcomp]

/-- Native closed adjunction and original Ext identify the input of the ambient Serre map. -/
def relativeClosedEmbeddingInputAddEquiv (Ω : X.Modules) (M : Z.Modules) (q : ℕ) :
    ((DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj Ω)))⟦(q : ℤ)⟧) ≃+
      Ext.{u + 1} ((Scheme.Modules.pushforward i).obj M) Ω q :=
  ((Scheme.Modules.closedImmersionRightAdjunction i).singleDerivedHomEquivOfInjectiveResolution
    M (injectiveResolution Ω) (q : ℤ)).symm.trans Ext.homAddEquiv.symm

variable (R : Type u) [CommRing R] (ι : Type u)
  (a : X ⟶ ProjectiveSpace R ι) (f : Y ⟶ Spec (.of R))
  (h : IsPullback a p (toSpec R ι) f) [Y.IsSeparated]

/-- The original Serre map transferred through the chosen embedding and actual right adjoint. -/
def relativeClosedEmbeddingSerreMap (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : Z.Modules) (q : ℕ) :
    ((DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧) →+
    (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus (i ≫ p)).obj
        ((DerivedCategory.Plus.singleFunctor Z.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧) := by
  let E := relativeClosedEmbeddingInputAddEquiv i
    ((relativeTopDifferentialCoefficientsFunctor p n).obj N) M q
  let D := DerivedCategory.Plus.ι.mapIso (relativeClosedEmbeddingPushforwardSingleIso i p M)
  let Φ := relativeProjectiveSerreMap R ι a p f h n e N ((Scheme.Modules.pushforward i).obj M) q
  exact {
    toFun x := D.hom ≫ Φ (E x)
    map_zero' := by rw [E.map_zero, Φ.map_zero, Limits.comp_zero]
    map_add' x y := by rw [E.map_add, Φ.map_add, Preadditive.comp_add] }

/-- Every supplied resolution gives exactly the same original adjunction inverse, ambient
Ext class, normalized trace comparison and geometric pushforward composition. -/
theorem relativeClosedEmbeddingSerreMap_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : Z.Modules) (q : ℕ)
    (I : InjectiveResolution ((relativeTopDifferentialCoefficientsFunctor p n).obj N))
    (x : (DerivedCategory.singleFunctor Z.Modules 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(q : ℤ)⟧) :
    relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q x =
      DerivedCategory.Plus.ι.map (relativeClosedEmbeddingPushforwardSingleIso i p M).hom ≫
        relativeProjectiveSerreMap R ι a p f h n e N ((Scheme.Modules.pushforward i).obj M) q
          (Ext.homEquiv.symm
            ((CategoryTheory.Adjunction.singleDerivedHomEquivOfInjectiveResolution
              (Scheme.Modules.closedImmersionRightAdjunction i) M I (q : ℤ)).symm x)) := by
  have hI := CategoryTheory.Adjunction.singleDerivedHomEquivOfInjectiveResolution_independent
    (Scheme.Modules.closedImmersionRightAdjunction i) M
      (injectiveResolution ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) (q : ℤ) I
  change DerivedCategory.Plus.ι.map (relativeClosedEmbeddingPushforwardSingleIso i p M).hom ≫
    relativeProjectiveSerreMap R ι a p f h n e N ((Scheme.Modules.pushforward i).obj M) q
      (Ext.homEquiv.symm
        ((CategoryTheory.Adjunction.singleDerivedHomEquivOfInjectiveResolution
          (Scheme.Modules.closedImmersionRightAdjunction i) M
            (injectiveResolution ((relativeTopDifferentialCoefficientsFunctor p n).obj N))
            (q : ℤ)).symm x)) = _
  rw [hI]

/-- The original chosen-embedding Serre map preserves arbitrary Ext precomposition.
The coefficient is its actual closed-right-adjoint value, without a purity or
coherent-duality premise. -/
theorem relativeClosedEmbeddingSerreMap_comp (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] {M M' : Z.Modules} {r j q : ℕ}
    (α : Ext.{u + 1} M M' r)
    (g : (DerivedCategory.singleFunctor Z.Modules 0).obj M' ⟶
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedClosedImmersionRightAdjointPlus i).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N))))⟦(j : ℤ)⟧)
    (hrj : r + j = q) :
    relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q
        (α.hom.comp g (by omega)) =
      (α.homPlus.map
        (Scheme.Modules.derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι)).comp
          (relativeClosedEmbeddingSerreMap i p R ι a f h n e N M' j g) (by omega) := by
  let Ω := (relativeTopDifferentialCoefficientsFunctor p n).obj N
  let I := injectiveResolution Ω
  let adj := Scheme.Modules.closedImmersionRightAdjunction i
  let E (T : Z.Modules) (k : ℕ) := relativeClosedEmbeddingInputAddEquiv i Ω T k
  let D (T : Z.Modules) := DerivedCategory.Plus.ι.mapIso
    (relativeClosedEmbeddingPushforwardSingleIso i p T)
  have hE : E M q (α.hom.comp g (by omega)) =
      (α.mapExactFunctor (Scheme.Modules.pushforward i)).comp (E M' j g) hrj := by
    apply Ext.ext
    rw [Ext.comp_hom]
    change Ext.homAddEquiv (Ext.homAddEquiv.symm
        ((adj.singleDerivedHomEquivOfInjectiveResolution M I (q : ℤ)).symm
          (α.hom.comp g (by omega)))) =
      (α.mapExactFunctor (Scheme.Modules.pushforward i)).hom.comp
        (Ext.homAddEquiv (Ext.homAddEquiv.symm
          ((adj.singleDerivedHomEquivOfInjectiveResolution M' I (j : ℤ)).symm g)))
        (show (j : ℤ) + (r : ℤ) = (q : ℤ) by omega)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact adj.singleDerivedHomEquivOfInjectiveResolution_symm_comp_ext
      I α (j : ℤ) (q : ℤ) (by omega) g
  have hD : (D M).hom ≫
        (α.mapExactFunctor (Scheme.Modules.pushforward i)).homPlus.map
          (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι) =
      α.homPlus.map
          (Scheme.Modules.derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι) ≫
        ((D M').hom)⟦(r : ℤ)⟧' :=
    relativeClosedEmbeddingPushforwardSingleIso_ext_naturality i p α
  change (D M).hom ≫
      relativeProjectiveSerreMap R ι a p f h n e N ((Scheme.Modules.pushforward i).obj M) q
        (E M q (α.hom.comp g (by omega))) =
    (α.homPlus.map
      (Scheme.Modules.derivedPushforwardPlus (i ≫ p) ⋙ DerivedCategory.Plus.ι)).comp
        ((D M').hom ≫ relativeProjectiveSerreMap R ι a p f h n e N
          ((Scheme.Modules.pushforward i).obj M') j (E M' j g)) (by omega)
  rw [hE, relativeProjectiveSerreMap_comp]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hD]

/-- The chosen-embedding transfer preserves bijectivity of the literal ambient comparison.
This uses the same closed adjunction and geometric composition as the displayed forward map. -/
theorem relativeClosedEmbeddingSerreMap_bijective_iff (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : Z.Modules) (q : ℕ) :
    Function.Bijective (relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q) ↔
      Function.Bijective
        (relativeProjectiveSerreMap R ι a p f h n e N
          ((Scheme.Modules.pushforward i).obj M) q) := by
  let E := relativeClosedEmbeddingInputAddEquiv i
    ((relativeTopDifferentialCoefficientsFunctor p n).obj N) M q
  let D := DerivedCategory.Plus.ι.mapIso (relativeClosedEmbeddingPushforwardSingleIso i p M)
  let Φ := relativeProjectiveSerreMap R ι a p f h n e N ((Scheme.Modules.pushforward i).obj M) q
  let B := Iso.homCongr D.symm
    (Iso.refl (((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧))
  have heq : (relativeClosedEmbeddingSerreMap i p R ι a f h n e N M q : _ → _) =
      B ∘ (Φ ∘ E) := by
    funext x
    change D.hom ≫ Φ (E x) = D.hom ≫ Φ (E x) ≫ 𝟙 _
    rw [Category.comp_id]
  rw [heq]
  exact (Equiv.comp_bijective (Φ ∘ E) B).trans (Equiv.bijective_comp E.toEquiv Φ)

end AlgebraicGeometry.Scheme.Cohomology
