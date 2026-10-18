/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Core
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.OpenPushforward
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.CompositionShift
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.Scalar
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# The original relative projective Serre comparison

Original Ext classes into the actual top differential coefficient are mapped by
native derived direct image and its installed shift comparison, then composed
with the shifted original normalized trace. The map is additive and preserves
original source and coefficient arrows. The base is separated; neither
Noetherianity nor flatness of the coefficient is used to construct the map.
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

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
  [Y.IsSeparated]

/-- The original full-category trace as an arrow in the installed bounded-below category. -/
def relativeProjectiveTracePlus (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] :
    (Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ⟶
      (DerivedCategory.Plus.singleFunctor Y.Modules (n : ℤ)).obj N :=
  DerivedCategory.Plus.ι.preimage (relativeProjectiveTrace R ι a p f h n e N)

/-- Inclusion carries the bounded-below trace to precisely the original full-category arrow. -/
theorem relativeProjectiveTracePlus_ι (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] :
    DerivedCategory.Plus.ι.map (relativeProjectiveTracePlus R ι a p f h n e N) =
      relativeProjectiveTrace R ι a p f h n e N :=
  Functor.map_preimage _ _

/-- The bounded-below trace retains the original coefficient naturality square. -/
@[reassoc]
theorem relativeProjectiveTracePlus_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {N N' : Y.Modules} [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    (Scheme.Modules.derivedPushforwardPlus p).map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
          ((relativeTopDifferentialCoefficientsFunctor p n).map s)) ≫
      relativeProjectiveTracePlus R ι a p f h n e N' =
    relativeProjectiveTracePlus R ι a p f h n e N ≫
      (DerivedCategory.Plus.singleFunctor Y.Modules (n : ℤ)).map s := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, relativeProjectiveTracePlus_ι]
  change _ = relativeProjectiveTrace R ι a p f h n e N ≫
    (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).map s
  exact relativeProjectiveTrace_naturality R ι a p f h n e s

/-- Native Ext maps to full derived Hom by original direct image followed by normalized trace. -/
def relativeProjectiveSerreMap (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules) (q : ℕ) :
    Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q →+
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
        ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧) := by
  let F := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  let t := ShiftedHom.mk₀ (0 : ℤ) rfl (relativeProjectiveTrace R ι a p f h n e N)
  refine {
    toFun := fun x => (x.homPlus.map F).comp t (zero_add _)
    map_zero' := ?_
    map_add' := fun x y => ?_ }
  · have hz : (0 : Ext.{u + 1} M
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q).homPlus = 0 :=
      (Ext.homPlusAddEquiv q).map_zero
    rw [hz, ShiftedHom.map_zero, ShiftedHom.zero_comp]
  · have hxy : (x + y).homPlus = x.homPlus + y.homPlus :=
      (Ext.homPlusAddEquiv q).map_add x y
    rw [hxy, ShiftedHom.map_add, ShiftedHom.add_comp]

/-- The forward arrow is literally the native shifted derived image followed by shifted trace. -/
theorem relativeProjectiveSerreMap_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules) (q : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q) :
    relativeProjectiveSerreMap R ι a p f h n e N M q x =
      x.homPlus.map (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι) ≫
        (shiftFunctor (DerivedCategory Y.Modules) (q : ℤ)).map
          (relativeProjectiveTrace R ι a p f h n e N) := by
  change (x.homPlus.map
    (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι)).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (relativeProjectiveTrace R ι a p f h n e N))
      (zero_add _) = _
  exact ShiftedHom.comp_mk₀ _ (0 : ℤ) rfl _

/-- The original comparison preserves Yoneda precomposition in every nonnegative degree. -/
theorem relativeProjectiveSerreMap_comp (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] {M M' : X.Modules} {i j q : ℕ}
    (x : Ext.{u + 1} M M' i)
    (y : Ext.{u + 1} M' ((relativeTopDifferentialCoefficientsFunctor p n).obj N) j)
    (hij : i + j = q) :
    relativeProjectiveSerreMap R ι a p f h n e N M q (x.comp y hij) =
      (x.homPlus.map (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι)).comp
        (relativeProjectiveSerreMap R ι a p f h n e N M' j y) (by omega) := by
  let F := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  let t := ShiftedHom.mk₀ (0 : ℤ) rfl (relativeProjectiveTrace R ι a p f h n e N)
  change ((x.comp y hij).homPlus.map F).comp t (zero_add _) =
    (x.homPlus.map F).comp ((y.homPlus.map F).comp t (zero_add _)) (by omega)
  rw [Ext.homPlus_comp, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ (by omega) (zero_add _) (by omega)

/-- Original source morphisms give the original derived-image precomposition square. -/
theorem relativeProjectiveSerreMap_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] {M M' : X.Modules} (s : M ⟶ M') (q : ℕ)
    (x : Ext.{u + 1} M' ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q) :
    relativeProjectiveSerreMap R ι a p f h n e N M q ((Ext.mk₀ s).comp x (zero_add q)) =
      (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι).map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map s) ≫
        relativeProjectiveSerreMap R ι a p f h n e N M' q x := by
  rw [relativeProjectiveSerreMap_comp, Ext.homPlus_mk₀]
  erw [ShiftedHom.map_mk₀]
  rw [ShiftedHom.mk₀_comp]

/-- Every original coefficient arrow acts by the corresponding shifted native single map. -/
theorem relativeProjectiveSerreMap_naturality_coefficients
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {N N' : Y.Modules}
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') (M : X.Modules) (q : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q) :
    relativeProjectiveSerreMap R ι a p f h n e N' M q
        (x.comp (Ext.mk₀ ((relativeTopDifferentialCoefficientsFunctor p n).map s))
          (Nat.add_zero q)) =
      relativeProjectiveSerreMap R ι a p f h n e N M q x ≫
        (shiftFunctor (DerivedCategory Y.Modules) (q : ℤ)).map
          ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).map s) := by
  let F := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  have ht := relativeProjectiveTrace_naturality R ι a p f h n e s
  change F.map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
      ((relativeTopDifferentialCoefficientsFunctor p n).map s)) ≫
      relativeProjectiveTrace R ι a p f h n e N' =
    relativeProjectiveTrace R ι a p f h n e N ≫
      (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).map s at ht
  rw [relativeProjectiveSerreMap_apply, relativeProjectiveSerreMap_apply,
    Ext.homPlus_comp, Ext.homPlus_mk₀, ShiftedHom.map_comp]
  erw [ShiftedHom.map_mk₀]
  rw [ShiftedHom.comp_mk₀, Category.assoc, ← Functor.map_comp, ht,
    Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
  [Y.IsSeparated]

/-- The original trace preserves any structural scalar through the original coefficient
endomorphism. No linearity instance for the right-derived functor is assumed. -/
theorem relativeProjectiveTrace_smul {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (r : S) :
    letI := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom Y α
    (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι).map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
          (r • 𝟙 ((relativeTopDifferentialCoefficientsFunctor p n).obj N))) ≫
      relativeProjectiveTrace R ι a p f h n e N =
        r • relativeProjectiveTrace R ι a p f h n e N := by
  let := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  let := relativeTopDifferentialCoefficientsFunctor_linearOfHom p α n
  have ht := relativeProjectiveTrace_naturality R ι a p f h n e (r • 𝟙 N)
  erw [(relativeTopDifferentialCoefficientsFunctor p n).map_smul,
    (relativeTopDifferentialCoefficientsFunctor p n).map_id,
    (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).map_smul,
    (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).map_id] at ht
  rw [Linear.comp_smul, Category.comp_id] at ht
  change (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι).map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
        (r • 𝟙 ((relativeTopDifferentialCoefficientsFunctor p n).obj N))) ≫
    relativeProjectiveTrace R ι a p f h n e N =
      r • relativeProjectiveTrace R ι a p f h n e N at ht
  exact ht

/-- The literal relative projective comparison, linear for every specified structural
ring action on the base and its original pullback action on the source. -/
def relativeProjectiveSerreLinearMap {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules) (q : ℕ) :
    letI := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
    letI := moduleCategoryLinearOfHom Y α
    Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q →ₗ[S]
      (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
        ((DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧) := by
  let := moduleCategoryLinearOfHom X (p.appTop.hom.comp α)
  let := moduleCategoryLinearOfHom Y α
  let F := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  refine { relativeProjectiveSerreMap R ι a p f h n e N M q with map_smul' := ?_ }
  intro r x
  have ht := relativeProjectiveTrace_smul R ι a p f h α n e N r
  change F.map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
      (r • 𝟙 ((relativeTopDifferentialCoefficientsFunctor p n).obj N))) ≫
    relativeProjectiveTrace R ι a p f h n e N =
      r • relativeProjectiveTrace R ι a p f h n e N at ht
  change relativeProjectiveSerreMap R ι a p f h n e N M q (r • x) =
    r • relativeProjectiveSerreMap R ι a p f h n e N M q x
  rw [relativeProjectiveSerreMap_apply, relativeProjectiveSerreMap_apply,
    Ext.smul_eq_comp_mk₀, Ext.homPlus_comp, Ext.homPlus_mk₀, ShiftedHom.map_comp]
  erw [ShiftedHom.map_mk₀]
  rw [ShiftedHom.comp_mk₀, Category.assoc, ← Functor.map_comp, ht,
    Functor.map_smul, Linear.comp_smul]

/-- The linear map retains exactly the original comparison as its forward function. -/
theorem relativeProjectiveSerreLinearMap_apply {S : Type u} [CommRing S]
    (α : S →+* Γ(Y, ⊤)) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules) (q : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q) :
    relativeProjectiveSerreLinearMap R ι a p f h α n e N M q x =
      relativeProjectiveSerreMap R ι a p f h n e N M q x := rfl

end AlgebraicGeometry.Scheme.Cohomology
