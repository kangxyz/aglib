/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Ext
public import Aglib.Algebra.Homology.Koszul.Top
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Original top Koszul Ext cocycles

For a finite weakly regular list, each coefficient defines a literal cocycle
on the original ordered top term of its native projective resolution. This
linear map represents every native top Ext class and retains original
coefficient maps as Yoneda postcomposition. In positive degree its zero
criterion uses the actual previous boundary of that same resolution.

The coefficient is arbitrary and the Ext size is independent of its carrier
universe. No coefficient regularity, flatness, finiteness or Noetherian
hypothesis is needed. The empty list is included in the class construction.
The quotient-line kernel, determinant changes of generators and geometric
purity are separate comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w

namespace ChainComplex.Koszul
variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

/-- The original ordered top Koszul cocycle defines a native Ext class for every coefficient. -/
def topExtClass (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) :
    N →ₗ[R] Ext (ModuleCat.of R (R ⧸ Ideal.ofList s)) N s.length := by
  let P := finiteProjectiveResolution s hs
  let c (x : N) : P.complex.X s.length ⟶ N :=
    (topComponentIso s).hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)
  have hc (x : N) : P.complex.d (s.length + 1) s.length ≫ c x = 0 :=
    (isZero_X s (s.length + 1) (by omega)).eq_of_src _ _
  refine {
    toFun := fun x => P.extMk (c x) (s.length + 1) rfl (hc x)
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    rw [P.add_extMk]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (topComponentIso s).hom z • (x + y) =
      (topComponentIso s).hom z • x + (topComponentIso s).hom z • y
    exact smul_add _ _ _
  · intro r x
    rw [Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (topComponentIso s).hom z • (r • x) = r • ((topComponentIso s).hom z • x)
    exact smul_comm _ _ _

/-- A coefficient is represented by the literal map from the original top resolution term. -/
theorem topExtClass_apply (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) (x : N) :
    topExtClass s hs N x =
      (finiteProjectiveResolution s hs).extMk
        ((topComponentIso s).hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))
        (s.length + 1) rfl
          ((isZero_X s (s.length + 1) (by omega)).eq_of_src _ _) := rfl

/-- Every native top Ext class comes from an original coefficient in the top Koszul term. -/
theorem topExtClass_surjective (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (N : ModuleCat.{u} R) :
    Function.Surjective (topExtClass s hs N) := by
  let P := finiteProjectiveResolution s hs
  intro e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (s.length + 1) rfl
  let f₀ : ModuleCat.of R R ⟶ N := (topComponentIso s).inv ≫ f
  have hF₀ : ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f₀.hom 1)) = f₀ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r • f₀.hom 1 = f₀.hom r
    simpa only [smul_eq_mul, mul_one] using (f₀.hom.map_smul r (1 : R)).symm
  have hF : (topComponentIso s).hom ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f₀.hom 1)) = f := by
    rw [hF₀]
    dsimp only [f₀]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine ⟨f₀.hom 1, ?_⟩
  rw [topExtClass_apply]
  change P.extMk ((topComponentIso s).hom ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f₀.hom 1)))
      (s.length + 1) rfl _ = P.extMk f (s.length + 1) rfl hf
  congr 1

/-- Original coefficient maps give the same cocycle and native Yoneda postcomposition. -/
@[simp]
theorem topExtClass_comp_mk₀ (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') (x : N) :
    (topExtClass s hs N x).comp (Ext.mk₀ g) (add_zero s.length) =
      topExtClass s hs N' (g x) := by
  rw [topExtClass_apply, topExtClass_apply, ProjectiveResolution.extMk_comp_mk₀]
  congr 1
  rw [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change g.hom (r • x) = r • g.hom x
  exact g.hom.map_smul r x


/-- In positive top degree, vanishing is the original nullhomotopy boundary equation. -/
theorem topExtClass_eq_zero_iff (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (N : ModuleCat.{u} R)
    (n : ℕ) (hn : n + 1 = s.length) (x : N) :
    topExtClass s hs N x = 0 ↔
      ∃ g : (chainComplex s).X n ⟶ N,
        (chainComplex s).d s.length n ≫ g =
          (topComponentIso s).hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x) := by
  rw [topExtClass_apply]
  exact (finiteProjectiveResolution s hs).extMk_eq_zero_iff
    _ (s.length + 1) rfl _ n hn

end ChainComplex.Koszul
