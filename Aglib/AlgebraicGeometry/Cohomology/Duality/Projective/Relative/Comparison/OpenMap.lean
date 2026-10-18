/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.OpenTrace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal

/-!
# The original Serre map under derived open restriction

The actual normalized trace equation and native shifted open comparison give
the forward-map restriction square in every nonnegative Ext degree. All
arrows are the installed derived images and original exact-single maps.
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

private theorem shifted_map_pre_post {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    {X' X Y Y' : C} (a : X' ⟶ X) {k : ℤ} (b : ShiftedHom X Y k) (c : Y ⟶ Y') :
    ShiftedHom.map (show ShiftedHom X' Y' k from a ≫ b ≫ c⟦k⟧') F =
      F.map a ≫ b.map F ≫ (F.map c)⟦k⟧' := by
  rw [← ShiftedHom.mk₀_comp (0 : ℤ) rfl a,
    ← ShiftedHom.comp_mk₀ b (0 : ℤ) rfl c,
    ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

variable {W X U Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ U) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)

variable (R : Type u) [CommRing R] (ι : Type u)
  (a : X ⟶ ProjectiveSpace R ι) (f : Y ⟶ Spec (.of R))
  (h : IsPullback a p (toSpec R ι) f) [Y.IsSeparated]

/-- The literal normalized comparison as an arrow in the installed bounded-below category. -/
def relativeProjectiveSerreMapPlus (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) r) :
    ShiftedHom ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))
      ((DerivedCategory.Plus.singleFunctor Y.Modules (n : ℤ)).obj N) (r : ℤ) :=
  x.homPlus.map (Scheme.Modules.derivedPushforwardPlus p) ≫
    (shiftFunctor (DerivedCategory.Plus Y.Modules) (r : ℤ)).map
      (relativeProjectiveTracePlus R ι a p f h n e N)

/-- The bounded-below arrow includes to exactly the original full-category Serre map. -/
theorem relativeProjectiveSerreMapPlus_ι (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) r) :
    (relativeProjectiveSerreMapPlus p R ι a f h n e N M r x).map DerivedCategory.Plus.ι =
      relativeProjectiveSerreMap R ι a p f h n e N M r x := by
  rw [relativeProjectiveSerreMap_apply, relativeProjectiveSerreMapPlus]
  rw [← ShiftedHom.comp_mk₀ (x.homPlus.map (Scheme.Modules.derivedPushforwardPlus p))
    (0 : ℤ) rfl (relativeProjectiveTracePlus R ι a p f h n e N)]
  rw [ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀,
    relativeProjectiveTracePlus_ι, ← ShiftedHom.comp_map]

/-- Bounded-below inclusion preserves and reflects bijectivity of the literal comparison. -/
theorem relativeProjectiveSerreMapPlus_bijective_iff (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules) (r : ℕ) :
    Function.Bijective (relativeProjectiveSerreMapPlus p R ι a f h n e N M r) ↔
      Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e N M r) := by
  let K := (Scheme.Modules.derivedPushforwardPlus p).obj
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let L := (DerivedCategory.Plus.singleFunctor Y.Modules (n : ℤ)).obj N
  let E : ShiftedHom K L (r : ℤ) ≃
      ShiftedHom (DerivedCategory.Plus.ι.obj K) (DerivedCategory.Plus.ι.obj L) (r : ℤ) :=
    (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).homEquiv.trans
      (Iso.homCongr (Iso.refl _) ((DerivedCategory.Plus.ι.commShiftIso (r : ℤ)).app L))
  have heq : (relativeProjectiveSerreMap R ι a p f h n e N M r : _ → _) =
      E ∘ relativeProjectiveSerreMapPlus p R ι a f h n e N M r := by
    funext x
    rw [← relativeProjectiveSerreMapPlus_ι]
    change _ = 𝟙 _ ≫ _ ≫ _
    rw [Category.id_comp]
    rfl
  rw [heq]
  exact (Equiv.comp_bijective (relativeProjectiveSerreMapPlus p R ι a f h n e N M r) E).symm

/-- Original coefficient naturality also holds in the native bounded-below category. -/
theorem relativeProjectiveSerreMapPlus_naturality_coefficients
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {N N' : Y.Modules}
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) r) :
    relativeProjectiveSerreMapPlus p R ι a f h n e N' M r
        (x.comp (Ext.mk₀ ((relativeTopDifferentialCoefficientsFunctor p n).map s))
          (Nat.add_zero r)) =
      relativeProjectiveSerreMapPlus p R ι a f h n e N M r x ≫
        ((DerivedCategory.Plus.singleFunctor Y.Modules (n : ℤ)).map s)⟦(r : ℤ)⟧' := by
  let F := Scheme.Modules.derivedPushforwardPlus p
  have ht := relativeProjectiveTracePlus_naturality R ι a p f h n e s
  rw [relativeProjectiveSerreMapPlus, relativeProjectiveSerreMapPlus,
    Ext.homPlus_comp, Ext.homPlus_mk₀, ShiftedHom.map_comp]
  erw [ShiftedHom.map_mk₀]
  rw [ShiftedHom.comp_mk₀, Category.assoc, ← Functor.map_comp, ht,
    Functor.map_comp, Category.assoc]

/-- The actual original-map square for every derived open restriction and every Ext degree. -/
theorem relativeProjectiveSerreMapPlus_open
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) r) :
    letI : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
    relativeProjectiveSerreMapPlus q R ι (i ≫ a) (j ≫ f) (H.paste_horiz h) n e
        (N.restrict j) (M.restrict i) r (relativeProjectiveExtRestriction p i q j H n N M r x) =
      (relativeProjectiveSourceRestrictionIso p i q j H M).inv ≫
        (relativeProjectiveSerreMapPlus p R ι a f h n e N M r x).map
          (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus ≫
        (shiftFunctor (DerivedCategory.Plus U.Modules) (r : ℤ)).map
          (((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusSingleIso (n : ℤ)).hom.app
            N) := by
  let : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
  let P := Scheme.Modules.derivedPushforwardPlus p
  let B := Scheme.Modules.derivedPushforwardPlus q
  let I := (Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlus
  let J := (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus
  let E := Scheme.Modules.derivedOpenBaseChangeIso i q p j H
  let sm := ((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).app M
  let sw := ((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).app
    ((relativeTopDifferentialCoefficientsFunctor p n).obj N)
  let c := (DerivedCategory.Plus.singleFunctor W.Modules 0).map
    ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N)
  let t := relativeProjectiveTracePlus R ι a p f h n e N
  let t' := relativeProjectiveTracePlus R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)
    n e (N.restrict j)
  let v := ((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusSingleIso (n : ℤ)).hom.app N
  have he := ShiftedHom.map_naturality_1 x.homPlus E
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at he
  have ht : E.hom.app ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ≫
      B.map sw.hom ≫ B.map c ≫ t' = J.map t ≫ v :=
    relativeProjectiveTracePlus_open R ι a p f h n e i q j H N
  rw [relativeProjectiveSerreMapPlus, relativeProjectiveExtRestriction_homPlus]
  rw [shifted_map_pre_post]
  simp only [Category.assoc]
  change B.map sm.inv ≫ (x.homPlus.map I).map B ≫ (B.map (sw.hom ≫ c))⟦(r : ℤ)⟧' ≫
      t'⟦(r : ℤ)⟧' = _
  rw [← ShiftedHom.comp_map]
  erw [← he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (shiftFunctor (DerivedCategory.Plus U.Modules) (r : ℤ)).map_comp,
    ← (shiftFunctor (DerivedCategory.Plus U.Modules) (r : ℤ)).map_comp,
    ← (shiftFunctor (DerivedCategory.Plus U.Modules) (r : ℤ)).map_comp, ht,
    (shiftFunctor (DerivedCategory.Plus U.Modules) (r : ℤ)).map_comp]
  change B.map sm.inv ≫ E.inv.app _ ≫ (x.homPlus.map (P ⋙ J)) ≫
      (J.map t)⟦(r : ℤ)⟧' ≫ v⟦(r : ℤ)⟧' = _
  have hpost := shifted_map_pre_post J (𝟙 _) (x.homPlus.map P) t
  simp only [Category.id_comp, CategoryTheory.Functor.map_id] at hpost
  change _ = (B.map sm.inv ≫ E.inv.app _) ≫
      ShiftedHom.map (show ShiftedHom _ _ (r : ℤ) from
        x.homPlus.map P ≫ t⟦(r : ℤ)⟧') J ≫ v⟦(r : ℤ)⟧'
  rw [hpost, ← ShiftedHom.comp_map]
  simp only [Category.assoc]

/-- Transport by scheme isomorphisms preserves bijectivity of the original Serre map. -/
theorem relativeProjectiveSerreMap_bijective_iff_of_isIso [IsIso i] [IsIso j]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : X.Modules) (r : ℕ) :
    letI : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
    Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e N M r) ↔
      Function.Bijective (relativeProjectiveSerreMap R ι (i ≫ a) q (j ≫ f)
        (H.paste_horiz h) n e (N.restrict j) (M.restrict i) r) := by
  let : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
  rw [← relativeProjectiveSerreMapPlus_bijective_iff,
    ← relativeProjectiveSerreMapPlus_bijective_iff]
  let A := relativeProjectiveExtRestriction p i q j H n N M r
  let B := relativeProjectiveTargetRestriction p i q j H (n : ℤ) N M (r : ℤ)
  let Φ := relativeProjectiveSerreMapPlus p R ι a f h n e N M r
  let Ψ := relativeProjectiveSerreMapPlus q R ι (i ≫ a) (j ≫ f) (H.paste_horiz h)
    n e (N.restrict j) (M.restrict i) r
  have heq : B ∘ Φ = Ψ ∘ A := by
    funext x
    exact (relativeProjectiveSerreMapPlus_open p i q j H R ι a f h n e N M r x).symm
  have hA := relativeProjectiveExtRestriction_bijective_of_isIso p i q j H n N M r
  have hB := relativeProjectiveTargetRestriction_bijective_of_isIso p i q j H (n : ℤ) N M (r : ℤ)
  change Function.Bijective Φ ↔ Function.Bijective Ψ
  have hb : Function.Bijective (B ∘ Φ) ↔ Function.Bijective (Ψ ∘ A) := by
    rw [heq]
  exact (Function.Bijective.of_comp_iff' hB Φ).symm.trans
    (hb.trans (Function.Bijective.of_comp_iff Ψ hA))

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y U : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f) [Y.IsSeparated]
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (j : U ⟶ Y) [IsOpenImmersion j] [IsAffineHom j]

/-- The original affine-open coefficient mate and the original derived counit give
the forward Serre square in every Ext degree. -/
theorem relativeProjectiveSerreMapPlus_openPushforward
    (L : U.Modules) [L.IsQuasicoherent] (M : X.Modules) (r : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj
      ((Scheme.Modules.pushforward j).obj L)) r) :
    letI : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
    letI : ((Scheme.Modules.pushforward j).obj L).IsQuasicoherent :=
      Scheme.Modules.QuasiCoherent.quasicoherent_pushforward_open j L
    relativeProjectiveSerreMapPlus (pullback.fst j p) R ι (pullback.snd j p ≫ a)
        (j ≫ f) ((IsPullback.of_hasPullback j p).flip.paste_horiz h) n e L
        (M.restrict (pullback.snd j p)) r (relativeOpenSourceRestriction p j n L M r x) =
      relativeOpenTargetRestriction p (pullback.snd j p) (pullback.fst j p) j
        (IsPullback.of_hasPullback j p).flip L M (n : ℤ) (r : ℤ)
        (relativeProjectiveSerreMapPlus p R ι a f h n e
          ((Scheme.Modules.pushforward j).obj L) M r x) := by
  let : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
  let : ((Scheme.Modules.pushforward j).obj L).IsQuasicoherent :=
    Scheme.Modules.QuasiCoherent.quasicoherent_pushforward_open j L
  rw [relativeOpenSourceRestriction,
    relativeProjectiveSerreMapPlus_naturality_coefficients (pullback.fst j p) R ι
      (pullback.snd j p ≫ a) (j ≫ f) ((IsPullback.of_hasPullback j p).flip.paste_horiz h),
    relativeProjectiveSerreMapPlus_open p (pullback.snd j p) (pullback.fst j p) j
      (IsPullback.of_hasPullback j p).flip R ι a f h]
  simp only [relativeOpenTargetRestriction, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Cohomology
