/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Boundary.Shift
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CoverSequence
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Coherent.Connecting
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The actual coefficient trace and the signed connecting square

The native single-shift isomorphism expresses the original trace in the third
vertex of the coefficient triangle shifted by minus the projective dimension.
Its connecting square retains the native sign and shift commutation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The native isomorphism from the shifted degree-zero single to the degree-n single. -/
def relativeCoefficientSingleShiftIso {Y : Scheme.{u}} (n : ℕ) (N : Y.Modules) :
    ((DerivedCategory.singleFunctor Y.Modules 0).obj N)⟦-(n : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N :=
  ((DerivedCategory.singleFunctors Y.Modules).shiftIso (-(n : ℤ)) (n : ℤ) 0
    (by omega)).app N

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
  [Y.IsSeparated]

/-- The original trace expressed using the native shifted degree-zero single. -/
def relativeProjectiveTraceShift (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] :
    (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ⟶
      ((DerivedCategory.singleFunctor Y.Modules 0).obj N)⟦-(n : ℤ)⟧ :=
  relativeProjectiveTrace R ι a p f h n e N ≫ (relativeCoefficientSingleShiftIso n N).inv

/-- Native transport of the actual coefficient naturality square. -/
@[reassoc]
theorem relativeProjectiveTraceShift_naturality
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {N N' : Y.Modules}
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι).map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
          ((relativeTopDifferentialCoefficientsFunctor p n).map s)) ≫
      relativeProjectiveTraceShift R ι a p f h n e N' =
    relativeProjectiveTraceShift R ι a p f h n e N ≫
      ((DerivedCategory.singleFunctor Y.Modules 0).map s)⟦-(n : ℤ)⟧' := by
  dsimp only [relativeProjectiveTraceShift, Functor.comp_map]
  rw [← Category.assoc, relativeProjectiveTrace_naturality, Category.assoc]
  simp only [Category.assoc]
  exact congrArg (fun z => relativeProjectiveTrace R ι a p f h n e N ≫ z)
    (((DerivedCategory.singleFunctors Y.Modules).shiftIso (-(n : ℤ)) (n : ℤ) 0
      (by omega)).inv.naturality s)

/-- The actual source triangle and original traces satisfy the signed native boundary square.
The epimorphism used to determine the third trace lies in the abelian heart. -/
theorem relativeProjectiveTraceShift_boundary
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent]
    (hW : (S.map (relativeTopDifferentialCoefficientsFunctor p n)).ShortExact) :
    ShiftedHom.map hW.singleTrianglePlus.mor₃
        (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι) ≫
      (relativeProjectiveTraceShift R ι a p f h n e S.X₁)⟦(1 : ℤ)⟧' =
    relativeProjectiveTraceShift R ι a p f h n e S.X₃ ≫
      ((-(n : ℤ)).negOnePow • hS.singleTriangle.mor₃⟦-(n : ℤ)⟧' ≫
        (shiftFunctorComm (DerivedCategory Y.Modules) (1 : ℤ) (-(n : ℤ))).hom.app
          hS.singleTriangle.obj₁) := by
  let F := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  let T := F.mapTriangle.obj hW.singleTrianglePlus
  have hT : T ∈ distTriang (DerivedCategory Y.Modules) :=
    F.map_distinguished _ hW.singleTrianglePlus_distinguished
  let : T.obj₁.IsLE (n : ℤ) :=
    relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e S.X₁
  let : T.obj₂.IsLE (n : ℤ) :=
    relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e S.X₂
  let : T.obj₃.IsLE (n : ℤ) :=
    relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e S.X₃
  apply DerivedCategory.triangle_shift_comm₃_of_epi_topHomology T hS.singleTriangle
    hT hS.singleTriangle_distinguished (n : ℤ) (-(n : ℤ)) S.X₃
    (relativeCoefficientSingleShiftIso n S.X₃)
    (relativeProjectiveTraceShift R ι a p f h n e S.X₁)
    (relativeProjectiveTraceShift R ι a p f h n e S.X₂)
    (relativeProjectiveTraceShift R ι a p f h n e S.X₃)
  · exact relativeProjectiveTraceShift_naturality R ι a p f h n e S.f
  · exact relativeProjectiveTraceShift_naturality R ι a p f h n e S.g

/-- The original comparison expressed in shifted degree-zero singles. -/
def relativeProjectiveSerreShiftMap (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] (M : X.Modules) (q : ℕ) :
    Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q →+
      ((Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ⟶
        (((DerivedCategory.singleFunctor Y.Modules 0).obj N)⟦-(n : ℤ)⟧)⟦(q : ℤ)⟧) := by
  let F := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  let t := ShiftedHom.mk₀ (0 : ℤ) rfl (relativeProjectiveTraceShift R ι a p f h n e N)
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

/-- This transport changes only the target by the installed native isomorphism. -/
theorem relativeProjectiveSerreShiftMap_apply
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : X.Modules) (q : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q) :
    relativeProjectiveSerreShiftMap R ι a p f h n e N M q x =
      relativeProjectiveSerreMap R ι a p f h n e N M q x ≫
        (relativeCoefficientSingleShiftIso n N).inv⟦(q : ℤ)⟧' := by
  change (x.homPlus.map _).comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl (relativeProjectiveTraceShift R ι a p f h n e N)) _ = _
  rw [ShiftedHom.comp_mk₀, relativeProjectiveSerreMap_apply]
  simp only [relativeProjectiveTraceShift, Functor.map_comp, Category.assoc]

/-- Native target transport preserves and reflects bijectivity of the literal map. -/
theorem relativeProjectiveSerreShiftMap_bijective_iff
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent]
    (M : X.Modules) (q : ℕ) :
    Function.Bijective (relativeProjectiveSerreShiftMap R ι a p f h n e N M q) ↔
      Function.Bijective (relativeProjectiveSerreMap R ι a p f h n e N M q) := by
  let E := (shiftFunctor (DerivedCategory Y.Modules) (q : ℤ)).mapIso
    (relativeCoefficientSingleShiftIso n N)
  constructor
  · intro hs
    constructor
    · intro x y hxy
      apply hs.injective
      rw [relativeProjectiveSerreShiftMap_apply, relativeProjectiveSerreShiftMap_apply, hxy]
    · intro y
      obtain ⟨x, hx⟩ := hs.surjective (y ≫ E.inv)
      refine ⟨x, ?_⟩
      apply (cancel_mono E.inv).mp
      exact (relativeProjectiveSerreShiftMap_apply R ι a p f h n e N M q x).symm.trans hx
  · intro hs
    constructor
    · intro x y hxy
      apply hs.injective
      apply (cancel_mono E.inv).mp
      exact (relativeProjectiveSerreShiftMap_apply R ι a p f h n e N M q x).symm.trans
        (hxy.trans (relativeProjectiveSerreShiftMap_apply R ι a p f h n e N M q y))
    · intro y
      obtain ⟨x, hx⟩ := hs.surjective (y ≫ E.hom)
      refine ⟨x, ?_⟩
      rw [relativeProjectiveSerreShiftMap_apply, hx]
      change (y ≫ E.hom) ≫ E.inv = y
      rw [Category.assoc, E.hom_inv_id, Category.comp_id]

/-- Original coefficient arrows retain the native shifted-single arrow after transport. -/
theorem relativeProjectiveSerreShiftMap_naturality_coefficients
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {N N' : Y.Modules}
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') (M : X.Modules) (q : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj N) q) :
    relativeProjectiveSerreShiftMap R ι a p f h n e N' M q
        (x.comp (Ext.mk₀ ((relativeTopDifferentialCoefficientsFunctor p n).map s))
          (Nat.add_zero q)) =
      relativeProjectiveSerreShiftMap R ι a p f h n e N M q x ≫
        (((DerivedCategory.singleFunctor Y.Modules 0).map s)⟦-(n : ℤ)⟧')⟦(q : ℤ)⟧' := by
  rw [relativeProjectiveSerreShiftMap_apply, relativeProjectiveSerreShiftMap_apply,
    relativeProjectiveSerreMap_naturality_coefficients]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (fun z => relativeProjectiveSerreMap R ι a p f h n e N M q x ≫
      (shiftFunctor (DerivedCategory Y.Modules) (q : ℤ)).map z)
    (((DerivedCategory.singleFunctors Y.Modules).shiftIso (-(n : ℤ)) (n : ℤ) 0
      (by omega)).inv.naturality s)

/-- The actual Yoneda connecting class maps to the native target connecting map. -/
theorem relativeProjectiveSerreShiftMap_extClass
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent]
    (hW : (S.map (relativeTopDifferentialCoefficientsFunctor p n)).ShortExact)
    (M : X.Modules) (q : ℕ)
    (x : Ext.{u + 1} M ((relativeTopDifferentialCoefficientsFunctor p n).obj S.X₃) q) :
    let K := (Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
    let T := (Triangle.shiftFunctor (DerivedCategory Y.Modules) (-(n : ℤ))).obj
      hS.singleTriangle
    relativeProjectiveSerreShiftMap R ι a p f h n e S.X₁ M (q + 1)
        (x.comp hW.extClass rfl) =
      (preadditiveCoyoneda.obj (Opposite.op K)).homologySequenceδ T (q : ℤ)
        ((q + 1 : ℕ) : ℤ) (by omega)
        (relativeProjectiveSerreShiftMap R ι a p f h n e S.X₃ M q x) := by
  let F := Scheme.Modules.derivedPushforwardPlus p ⋙ DerivedCategory.Plus.ι
  let T := (Triangle.shiftFunctor (DerivedCategory Y.Modules) (-(n : ℤ))).obj
    hS.singleTriangle
  change ((x.comp hW.extClass rfl).homPlus.map F).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (relativeProjectiveTraceShift R ι a p f h n e S.X₁))
      (zero_add _) =
    (preadditiveCoyoneda.obj
      (Opposite.op (F.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)))).homologySequenceδ
        T (q : ℤ) ((q + 1 : ℕ) : ℤ) (by omega)
        ((x.homPlus.map F).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (relativeProjectiveTraceShift R ι a p f h n e S.X₃))
          (zero_add _))
  rw [ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀]
  exact Ext.map_homPlus_extClass_postcomp F hW T
    (relativeProjectiveTraceShift R ι a p f h n e S.X₁)
    (relativeProjectiveTraceShift R ι a p f h n e S.X₃)
    (relativeProjectiveTraceShift_boundary R ι a p f h n e hS hW) M q x

end AlgebraicGeometry.Scheme.Cohomology
