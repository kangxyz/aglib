/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.TotalComplex.NatSigns
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
/-!
# Canonical maps to first-quadrant cochain total complexes

The theorem `quasiIso_total_of_rowwise` proves that rowwise quasi-isomorphisms
induce a quasi-isomorphism of the native total complex over an arbitrary ring.
The proof uses elementwise cycle and boundary lifting and finite antidiagonal
elimination; no row splitting, dimension bound, or upper degree bound is assumed.

The single-zero comparison is the actual coproduct injection. Augmentations
and their naturality use the native total functor, and changing axes uses its
signed flip isomorphism. The ring and module universes are independent.

Extraction source: `R5Lab.CategoryTheory.Homology.FirstQuadrantComparison` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂

universe u v

namespace HomologicalComplex₂

variable (R : Type u) [Ring R]

/-- Bicomplexes in two nonnegative cochain degrees. -/
abbrev FirstQuadrant :=
  HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)

/-- The native functor concentrating the second degree in zero. -/
abbrev SingleSecondZero : CochainComplex (ModuleCat.{v} R) ℕ ⥤ FirstQuadrant.{u, v} R :=
  (CochainComplex.single₀ (ModuleCat.{v} R)).mapHomologicalComplex (.up ℕ)

variable {R}

/-- Inclusion of a cochain complex in the `(n,0)` summand of its totalization. -/
def singleSecondZeroTotalInclusion (L : CochainComplex (ModuleCat.{v} R) ℕ) :
    L ⟶ ((SingleSecondZero.{u, v} R).obj L).total (.up ℕ) where
  f n := ((SingleSecondZero.{u, v} R).obj L).ιTotal (.up ℕ) n 0 n (Nat.add_zero n)
  comm' i j h := by
    change _ ≫ (((SingleSecondZero.{u, v} R).obj L).D₁ (.up ℕ) i j +
      ((SingleSecondZero.{u, v} R).obj L).D₂ (.up ℕ) i j) = L.d i j ≫ _
    rw [Preadditive.comp_add, ι_D₁, ι_D₂,
      d₁_eq _ _ h 0 j (Nat.add_zero j),
      d₂_eq' _ _ i (show (ComplexShape.up ℕ).Rel 0 1 from rfl) j]
    simp [SingleSecondZero, ComplexShape.ε₁]

/-- Projection away from the zero objects in positive second degree. -/
def singleSecondZeroTotalProjection (L : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (((SingleSecondZero.{u, v} R).obj L).total (.up ℕ)).X n ⟶ L.X n :=
  ((SingleSecondZero.{u, v} R).obj L).totalDesc fun p q h ↦
    if hq : q = 0 then by
      subst q
      have hp : p = n := by simpa using h
      subst p
      exact 𝟙 _
    else 0

@[reassoc (attr := simp)]
theorem singleSecondZeroTotalInclusion_projection
    (L : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (singleSecondZeroTotalInclusion L).f n ≫ singleSecondZeroTotalProjection L n = 𝟙 _ := by
  simp [singleSecondZeroTotalInclusion, singleSecondZeroTotalProjection, SingleSecondZero]

@[reassoc (attr := simp)]
theorem singleSecondZeroTotalProjection_inclusion
    (L : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    singleSecondZeroTotalProjection L n ≫ (singleSecondZeroTotalInclusion L).f n = 𝟙 _ := by
  apply total.hom_ext
  intro p q h
  by_cases hq : q = 0
  · subst q
    have hp : p = n := by simpa using h
    subst p
    simp [singleSecondZeroTotalProjection, singleSecondZeroTotalInclusion]
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 (L.X p) q hq).eq_of_src

instance singleSecondZeroTotalInclusion_f_isIso
    (L : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    IsIso ((singleSecondZeroTotalInclusion L).f n) :=
  ⟨⟨singleSecondZeroTotalProjection L n, singleSecondZeroTotalInclusion_projection L n,
    singleSecondZeroTotalProjection_inclusion L n⟩⟩

/-- The canonical total isomorphism for concentration in second degree zero. -/
def singleSecondZeroTotalIso (L : CochainComplex (ModuleCat.{v} R) ℕ) :
    L ≅ ((SingleSecondZero.{u, v} R).obj L).total (.up ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso ((singleSecondZeroTotalInclusion L).f n))
    (fun i j _ ↦ (singleSecondZeroTotalInclusion L).comm i j)

@[simp]
theorem singleSecondZeroTotalIso_hom (L : CochainComplex (ModuleCat.{v} R) ℕ) :
    (singleSecondZeroTotalIso L).hom = singleSecondZeroTotalInclusion L := rfl

/-- The component formula is retained; simplification uses `singleSecondZeroTotalIso_hom`. -/
theorem singleSecondZeroTotalIso_hom_f (L : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (singleSecondZeroTotalIso L).hom.f n =
      ((SingleSecondZero.{u, v} R).obj L).ιTotal (.up ℕ) n 0 n (Nat.add_zero n) := rfl

@[reassoc]
theorem singleSecondZeroTotalIso_naturality
    {L L' : CochainComplex (ModuleCat.{v} R) ℕ} (f : L ⟶ L') :
    f ≫ (singleSecondZeroTotalIso L').hom =
      (singleSecondZeroTotalIso L).hom ≫ total.map ((SingleSecondZero.{u, v} R).map f) (.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp [singleSecondZeroTotalInclusion, SingleSecondZero]

/-- The actual total map induced by an augmentation into a bicomplex. -/
def totalAugmentation {L : CochainComplex (ModuleCat.{v} R) ℕ} {B : FirstQuadrant.{u, v} R}
    (α : (SingleSecondZero.{u, v} R).obj L ⟶ B) : L ⟶ B.total (.up ℕ) :=
  (singleSecondZeroTotalIso L).hom ≫ total.map α (.up ℕ)

@[simp]
theorem totalAugmentation_f {L : CochainComplex (ModuleCat.{v} R) ℕ} {B : FirstQuadrant.{u, v} R}
    (α : (SingleSecondZero.{u, v} R).obj L ⟶ B) (n : ℕ) :
    (totalAugmentation α).f n = (α.f n).f 0 ≫ B.ιTotal (.up ℕ) n 0 n (Nat.add_zero n) := by
  simp [totalAugmentation, singleSecondZeroTotalInclusion]

/-- A commuting augmentation square induces the same commuting square on actual totals. -/
@[reassoc]
theorem totalAugmentation_naturality
    {L L' : CochainComplex (ModuleCat.{v} R) ℕ} {B B' : FirstQuadrant.{u, v} R}
    (α : (SingleSecondZero.{u, v} R).obj L ⟶ B) (α' : (SingleSecondZero.{u, v} R).obj L' ⟶ B')
    (f : L ⟶ L') (g : B ⟶ B')
    (h : (SingleSecondZero.{u, v} R).map f ≫ α' = α ≫ g) :
    f ≫ totalAugmentation α' = totalAugmentation α ≫ total.map g (.up ℕ) := by
  simp only [totalAugmentation, ← Category.assoc]
  rw [singleSecondZeroTotalIso_naturality, Category.assoc, ← total.map_comp, h,
    total.map_comp, Category.assoc]

/-- Naturality of the native signed flip isomorphism. -/
@[reassoc]
theorem totalFlipIso_naturality {B C : FirstQuadrant.{u, v} R} (φ : B ⟶ C) :
    total.map ((flipFunctor (ModuleCat.{v} R) (.up ℕ) (.up ℕ)).map φ) (.up ℕ) ≫
      (C.totalFlipIso (.up ℕ)).hom =
    (B.totalFlipIso (.up ℕ)).hom ≫ total.map φ (.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (total.map _ (.up ℕ)).f n ≫ (C.totalFlipIso (.up ℕ)).hom.f n =
    (B.totalFlipIso (.up ℕ)).hom.f n ≫ (total.map φ (.up ℕ)).f n
  apply total.hom_ext
  intro q p h
  simp

/-- On bidegree `(q,p)` of the flipped complex, the flip has Koszul sign `(-1)^(p*q)`. -/
@[reassoc]
theorem ιTotal_totalFlipIso_hom (B : FirstQuadrant.{u, v} R) (p q n : ℕ) (h : q + p = n) :
    B.flip.ιTotal (.up ℕ) q p n h ≫ (B.totalFlipIso (.up ℕ)).hom.f n =
      (-1 : ℤˣ) ^ (p * q) • B.ιTotal (.up ℕ) p q n (by change p + q = n; omega) := by
  exact B.ιTotal_totalFlipIso_f_hom (.up ℕ) p q n h

/-- The augmentation on the other axis, followed by the native signed flip. -/
def totalAugmentationFlip {L : CochainComplex (ModuleCat.{v} R) ℕ} {B : FirstQuadrant.{u, v} R}
    (α : (SingleSecondZero.{u, v} R).obj L ⟶ B.flip) : L ⟶ B.total (.up ℕ) :=
  totalAugmentation α ≫ (B.totalFlipIso (.up ℕ)).hom

@[simp]
theorem totalAugmentationFlip_f {L : CochainComplex (ModuleCat.{v} R) ℕ}
    {B : FirstQuadrant.{u, v} R} (α : (SingleSecondZero.{u, v} R).obj L ⟶ B.flip) (n : ℕ) :
    (totalAugmentationFlip α).f n =
      (α.f n).f 0 ≫ B.ιTotal (.up ℕ) 0 n n (Nat.zero_add n) := by
  simp [totalAugmentationFlip]

/-- A commuting square on the flipped axis commutes after the signed identification. -/
@[reassoc]
theorem totalAugmentationFlip_naturality
    {L L' : CochainComplex (ModuleCat.{v} R) ℕ} {B B' : FirstQuadrant.{u, v} R}
    (α : (SingleSecondZero.{u, v} R).obj L ⟶ B.flip)
    (α' : (SingleSecondZero.{u, v} R).obj L' ⟶ B'.flip)
    (f : L ⟶ L') (g : B ⟶ B')
    (h : (SingleSecondZero.{u, v} R).map f ≫ α' =
      α ≫ (flipFunctor (ModuleCat.{v} R) (.up ℕ) (.up ℕ)).map g) :
    f ≫ totalAugmentationFlip α' = totalAugmentationFlip α ≫ total.map g (.up ℕ) := by
  simp only [totalAugmentationFlip, ← Category.assoc]
  rw [totalAugmentation_naturality α α' f _ h, Category.assoc,
    totalFlipIso_naturality, Category.assoc]

end HomologicalComplex₂

namespace HomologicalComplex₂

/-- The actual finite antidiagonal indexing a total degree. -/
abbrev TotalDegree (n : ℕ) :=
  ((ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
    (ComplexShape.up ℕ)) ⁻¹' ({n} : Set ℕ))

/-- Enumerate a first-quadrant antidiagonal without changing its original indices. -/
def totalDegreeEquiv (n : ℕ) : Fin (n + 1) ≃ TotalDegree n where
  toFun i := ⟨(i.val, n - i.val), by change i.val + (n - i.val) = n; have := i.isLt; omega⟩
  invFun p := ⟨p.val.1, by have hp : p.val.1 + p.val.2 = n := p.property; omega⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      have hp : p.val.1 + p.val.2 = n := p.property
      omega

/-- Each total degree has finitely many first-quadrant summands. -/
instance (n : ℕ) : Fintype (TotalDegree n) := Fintype.ofEquiv _ (totalDegreeEquiv n)

variable {R : Type u} [Ring R]

variable (K : HomologicalComplex₂ (ModuleCat.{v} R)
  (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- Projection onto an original summand of the actual total complex. -/
def totalCoordinate (n : ℕ) (p : TotalDegree n) :
    (K.total (ComplexShape.up ℕ)).X n ⟶ (K.X p.val.1).X p.val.2 :=
  Sigma.π (K.toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) n) p

/-- Inclusion of the original antidiagonal summand. -/
def totalSummand (n : ℕ) (p : TotalDegree n) :
    (K.X p.val.1).X p.val.2 ⟶ (K.total (ComplexShape.up ℕ)).X n :=
  K.ιTotal (ComplexShape.up ℕ) p.val.1 p.val.2 n p.property

/-- The actual summand projection is a retraction of its original inclusion. -/
@[reassoc (attr := simp)]
theorem totalSummand_coordinate_self (n : ℕ) (p : TotalDegree n) :
    totalSummand K n p ≫ totalCoordinate K n p = 𝟙 _ := by
  change Sigma.ι _ p ≫ Sigma.π _ p = _
  rw [Sigma.ι_π]
  simp only [dite_true, eqToHom_refl]
  rfl

/-- Distinct total summands have zero cross-coordinate maps. -/
@[reassoc (attr := simp)]
theorem totalSummand_coordinate_ne (n : ℕ) (p q : TotalDegree n) (h : p ≠ q) :
    totalSummand K n p ≫ totalCoordinate K n q = 0 := by
  change Sigma.ι _ p ≫ Sigma.π _ q = _
  rw [Sigma.ι_π]
  simp [h]

/-- Finite antidiagonal coordinates reconstruct the actual total module. -/
theorem totalCoordinate_sum (n : ℕ) :
    ∑ p : TotalDegree n, totalCoordinate K n p ≫ totalSummand K n p = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro p
  change totalSummand K n p ≫ _ = totalSummand K n p ≫ _
  rw [Preadditive.comp_sum]
  simp only [Category.comp_id, ← Category.assoc]
  rw [Finset.sum_eq_single p]
  · rw [totalSummand_coordinate_self, Category.id_comp]
  · intro q _ hq
    rw [totalSummand_coordinate_ne K n p q hq.symm, zero_comp]
  · simp

/-- The actual total differential has its two signed summand components. -/
theorem totalSummand_d (n m : ℕ) (p : TotalDegree n) :
    totalSummand K n p ≫ (K.total (ComplexShape.up ℕ)).d n m =
      K.d₁ (ComplexShape.up ℕ) p.val.1 p.val.2 m +
        K.d₂ (ComplexShape.up ℕ) p.val.1 p.val.2 m := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add]
  exact congrArg₂ (· + ·) (K.ι_D₁ _ _ _ _ _ _) (K.ι_D₂ _ _ _ _ _ _)

/-- Actual coordinates separate elements of every total module. -/
theorem totalCoordinate_ext (n : ℕ) (x y : (K.total (ComplexShape.up ℕ)).X n)
    (h : ∀ p : TotalDegree n, totalCoordinate K n p x = totalCoordinate K n p y) : x = y := by
  have hx := congrArg (fun f => f x) (totalCoordinate_sum K n)
  have hy := congrArg (fun f => f y) (totalCoordinate_sum K n)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] at hx hy
  rw [← hx, ← hy]
  exact Finset.sum_congr rfl (fun p _ => congrArg (totalSummand K n p) (h p))

/-- The two outgoing summands, with the native cochain signs. -/
theorem totalSummand_d_up (n p q : ℕ) (h : p + q = n) :
    K.ιTotal (.up ℕ) p q n h ≫ (K.total (.up ℕ)).d n (n + 1) =
      (K.d p (p + 1)).f q ≫ K.ιTotal (.up ℕ) (p + 1) q (n + 1) (by
        change p + 1 + q = n + 1; omega) +
      (-1 : ℤˣ) ^ p • ((K.X p).d q (q + 1) ≫
        K.ιTotal (.up ℕ) p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq K _ (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl) q _ (by
      change p + 1 + q = n + 1; omega),
    HomologicalComplex₂.d₂_eq K _ p (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl) _ (by
      change p + (q + 1) = n + 1; omega)]
  simp

@[reassoc]
theorem ιTotal_coordinate_ne_outer (n i j : ℕ) (h : i + j = n)
    (p : TotalDegree n) (hi : i ≠ p.val.1) :
    K.ιTotal (.up ℕ) i j n h ≫ totalCoordinate K n p = 0 := by
  apply totalSummand_coordinate_ne K n ⟨(i, j), h⟩ p
  intro heq
  exact hi (congrArg (fun a : TotalDegree n ↦ a.val.1) heq)

theorem totalSummand_d_coordinate_eq_zero (n : ℕ)
    (s : TotalDegree n) (t : TotalDegree (n + 1))
    (h₀ : s.val.1 ≠ t.val.1) (h₁ : s.val.1 + 1 ≠ t.val.1) :
    totalSummand K n s ≫ (K.total (.up ℕ)).d n (n + 1) ≫
      totalCoordinate K (n + 1) t = 0 := by
  rw [← Category.assoc]
  change (K.ιTotal (.up ℕ) s.val.1 s.val.2 n s.property ≫ _) ≫ _ = 0
  rw [totalSummand_d_up, Preadditive.add_comp, Linear.units_smul_comp]
  simp only [Category.assoc, ιTotal_coordinate_ne_outer K _ _ _ _ t h₀,
    ιTotal_coordinate_ne_outer K _ _ _ _ t h₁, comp_zero, smul_zero, add_zero]

/-- All components in outer degrees below `k` vanish. -/
def TotalSupportedFrom (n k : ℕ) (x : (K.total (.up ℕ)).X n) : Prop :=
  ∀ s : TotalDegree n, s.val.1 < k → totalCoordinate K n s x = 0

/-- On the first possibly nonzero component, the total cycle equation is the row cycle equation. -/
theorem totalCoordinate_d_of_support (n p q : ℕ) (h : p + q = n)
    (x : (K.total (.up ℕ)).X n) (hx : TotalSupportedFrom K n p x) :
    totalCoordinate K (n + 1)
      ⟨(p, q + 1), by change p + (q + 1) = n + 1; omega⟩
      ((K.total (.up ℕ)).d n (n + 1) x) =
    ((-1 : ℤˣ) ^ p • (K.X p).d q (q + 1))
      (totalCoordinate K n ⟨(p,q), h⟩ x) := by
  classical
  let s₀ : TotalDegree n := ⟨(p,q), h⟩
  let t : TotalDegree (n + 1) := ⟨(p,q + 1), by change p + (q + 1) = n + 1; omega⟩
  have he : ∑ s : TotalDegree n, totalSummand K n s (totalCoordinate K n s x) = x := by
    simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.comp_apply,
      ModuleCat.id_apply] using congrArg (fun f ↦ f x) (totalCoordinate_sum K n)
  conv_lhs => rw [← he, map_sum, map_sum]
  rw [Finset.sum_eq_single s₀]
  · have hm : totalSummand K n s₀ ≫ (K.total (.up ℕ)).d n (n + 1) ≫
        totalCoordinate K (n + 1) t = (-1 : ℤˣ)^p • (K.X p).d q (q + 1) := by
      rw [← Category.assoc]
      change (K.ιTotal (.up ℕ) p q n h ≫ _) ≫ _ = _
      rw [totalSummand_d_up, Preadditive.add_comp, Linear.units_smul_comp,
        Category.assoc, ιTotal_coordinate_ne_outer K _ _ _ _ t (by dsimp [t]; omega),
        comp_zero, zero_add]
      change (-1 : ℤˣ)^p • (_ ≫ (totalSummand K (n + 1) t ≫ totalCoordinate K (n + 1) t)) = _
      rw [totalSummand_coordinate_self, Category.comp_id]
    exact congrArg (fun f ↦ f (totalCoordinate K n s₀ x)) hm
  · intro s _ hs
    by_cases hlt : s.val.1 < p
    · rw [hx s hlt, map_zero, map_zero, map_zero]
    · have hne : s.val.1 ≠ p := by
        intro hp
        apply hs
        apply Subtype.ext
        apply Prod.ext hp
        have hh : s.val.1 + s.val.2 = n := s.property
        dsimp [s₀]
        omega
      have hm := totalSummand_d_coordinate_eq_zero K n s t hne (by dsimp [t]; omega)
      exact congrArg (fun f ↦ f (totalCoordinate K n s x)) hm
  · simp

theorem totalSummand_d_coordinate_vertical (n p q : ℕ) (h : p + q = n) :
    K.ιTotal (.up ℕ) p q n h ≫ (K.total (.up ℕ)).d n (n + 1) ≫
      totalCoordinate K (n + 1) ⟨(p,q + 1), by change p + (q + 1) = n + 1; omega⟩ =
        (-1 : ℤˣ)^p • (K.X p).d q (q + 1) := by
  rw [← Category.assoc, totalSummand_d_up, Preadditive.add_comp, Linear.units_smul_comp,
    Category.assoc, ιTotal_coordinate_ne_outer K _ _ _ _ _ (by dsimp; omega),
    comp_zero, zero_add]
  change (-1 : ℤˣ)^p • ((K.X p).d q (q + 1) ≫
    (totalSummand K (n + 1) ⟨(p,q + 1), by change p + (q + 1) = n + 1; omega⟩ ≫
      totalCoordinate K (n + 1) ⟨(p,q + 1), by change p + (q + 1) = n + 1; omega⟩)) = _
  rw [totalSummand_coordinate_self, Category.comp_id]

theorem totalSummand_d_coordinate_eq_zero' (n m : ℕ) (hm : n + 1 = m)
    (s : TotalDegree n) (t : TotalDegree m)
    (h₀ : s.val.1 ≠ t.val.1) (h₁ : s.val.1 + 1 ≠ t.val.1) :
    totalSummand K n s ≫ (K.total (.up ℕ)).d n m ≫ totalCoordinate K m t = 0 := by
  subst m
  exact totalSummand_d_coordinate_eq_zero K n s t h₀ h₁

theorem totalSummand_d_coordinate_vertical' (n m p q : ℕ) (h : p + q = n) (hm : n + 1 = m) :
    K.ιTotal (.up ℕ) p q n h ≫ (K.total (.up ℕ)).d n m ≫
      totalCoordinate K m ⟨(p,q + 1), by change p + (q + 1) = m; omega⟩ =
        (-1 : ℤˣ)^p • (K.X p).d q (q + 1) := by
  subst m
  exact totalSummand_d_coordinate_vertical K n p q h

private theorem row_boundary (hK : ∀ p q, (K.X p).ExactAt q) (p q : ℕ)
    (x : (K.X p).X q) (hx : (K.X p).d q (q + 1) x = 0) :
    ∃ y : (K.X p).X (q - 1), (K.X p).d (q - 1) q y = x := by
  have hh := hK p q
  rw [(K.X p).exactAt_iff' (q - 1) q (q + 1) (by
    cases q with
    | zero => exact (ComplexShape.up ℕ).prev_eq_self' 0 (by intro i; change ¬i + 1 = 0; omega)
    | succ q => exact (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel q (q + 1) from
      rfl))
    ((ComplexShape.up ℕ).next_eq' rfl)] at hh
  exact (ShortComplex.moduleCat_exact_iff _).mp hh x hx

/-- Every total cycle of a first-quadrant bicomplex with exact rows is a boundary.
The proof eliminates the finitely many antidiagonal components in increasing outer degree. -/
theorem total_cycle_boundary_of_rowwise_exact
    (hK : ∀ p q, (K.X p).ExactAt q) (n : ℕ)
    (x : (K.total (.up ℕ)).X n) (hx : (K.total (.up ℕ)).d n (n + 1) x = 0) :
    ∃ y : (K.total (.up ℕ)).X (n - 1), (K.total (.up ℕ)).d (n - 1) n y = x := by
  classical
  let P (k : ℕ) := ∀ z : (K.total (.up ℕ)).X n,
    (K.total (.up ℕ)).d n (n + 1) z = 0 → TotalSupportedFrom K n k z →
    ∃ y : (K.total (.up ℕ)).X (n - 1), (K.total (.up ℕ)).d (n - 1) n y = z
  have base : P (n + 1) := by
    intro z _ hz
    have he : z = 0 := by
      apply totalCoordinate_ext K n
      intro s
      rw [map_zero]
      apply hz s
      have hh : s.val.1 + s.val.2 = n := s.property
      omega
    exact ⟨0, by rw [map_zero, he]⟩
  have step : ∀ k, k < n + 1 → P (k + 1) → P k := by
    intro k hk ih z hdz hz
    obtain ⟨q, hq⟩ : ∃ q, k + q = n := ⟨n - k, by omega⟩
    have hv : (K.X k).d q (q + 1) (totalCoordinate K n ⟨(k,q),hq⟩ z) = 0 := by
      have hd := totalCoordinate_d_of_support K n k q hq z hz
      rw [hdz, map_zero] at hd
      change (0 : (K.X k).X (q + 1)) = (-1 : ℤˣ)^k •
        (K.X k).d q (q + 1) (totalCoordinate K n ⟨(k,q),hq⟩ z) at hd
      exact (smul_eq_zero_iff_eq ((-1 : ℤˣ)^k)).mp hd.symm
    obtain ⟨w, hw⟩ := row_boundary K hK k q _ hv
    cases q with
    | zero =>
      have hv0 : totalCoordinate K n ⟨(k,0),hq⟩ z = 0 := by
        rw [(K.X k).shape 0 0 (by simp)] at hw
        exact hw.symm
      apply ih z hdz
      intro s hs
      by_cases hsk : s.val.1 < k
      · exact hz s hsk
      · have he : s = ⟨(k,0),hq⟩ := by
          apply Subtype.ext
          apply Prod.ext <;> dsimp
          · omega
          · have hh : s.val.1 + s.val.2 = n := s.property
            omega
        rw [he]
        exact hv0
    | succ q =>
      change (K.X k).d q (q + 1) w = totalCoordinate K n ⟨(k,q + 1),hq⟩ z at hw
      have hq' : k + q = n - 1 := by omega
      let s₀ : TotalDegree (n - 1) := ⟨(k,q),hq'⟩
      let t₀ : TotalDegree n := ⟨(k,q + 1),hq⟩
      let b : (K.total (.up ℕ)).X (n - 1) :=
        ((-1 : ℤˣ)^k • totalSummand K (n - 1) s₀) w
      let z' := z - (K.total (.up ℕ)).d (n - 1) n b
      have hdz' : (K.total (.up ℕ)).d n (n + 1) z' = 0 := by
        dsimp [z']
        rw [map_sub, hdz]
        have hh := congrArg (fun f ↦ f b) ((K.total (.up ℕ)).d_comp_d (n - 1) n (n + 1))
        change (K.total (.up ℕ)).d n (n + 1) ((K.total (.up ℕ)).d (n - 1) n b) = 0 at hh
        rw [hh, sub_zero]
      have hsup : TotalSupportedFrom K n (k + 1) z' := by
        intro s hs
        change totalCoordinate K n s (z - (K.total (.up ℕ)).d (n - 1) n b) = 0
        rw [map_sub]
        by_cases hsk : s.val.1 < k
        · rw [hz s hsk]
          have hh : ((-1 : ℤˣ)^k • totalSummand K (n - 1) s₀) ≫
              (K.total (.up ℕ)).d (n - 1) n ≫ totalCoordinate K n s = 0 := by
            rw [Linear.units_smul_comp]
            have hn : n - 1 + 1 = n := by omega
            have hh := totalSummand_d_coordinate_eq_zero' K (n - 1) n hn s₀ s
              (by dsimp [s₀]; omega) (by dsimp [s₀]; omega)
            rw [hh, smul_zero]
          have hb := congrArg (fun f ↦ f w) hh
          change totalCoordinate K n s ((K.total (.up ℕ)).d (n - 1) n b) = 0 at hb
          rw [hb, sub_zero]
        · have he : s = t₀ := by
            apply Subtype.ext
            apply Prod.ext <;> dsimp [t₀]
            · omega
            · have hh : s.val.1 + s.val.2 = n := s.property
              omega
          subst s
          have hh : ((-1 : ℤˣ)^k • totalSummand K (n - 1) s₀) ≫
              (K.total (.up ℕ)).d (n - 1) n ≫ totalCoordinate K n t₀ =
              (K.X k).d q (q + 1) := by
            rw [Linear.units_smul_comp]
            have hn : n - 1 + 1 = n := by omega
            have hh := totalSummand_d_coordinate_vertical' K (n - 1) n k q hq' hn
            change totalSummand K (n - 1) s₀ ≫ _ ≫ totalCoordinate K n t₀ = _ at hh
            rw [hh, smul_smul, Int.units_mul_self, one_smul]
          have hb := congrArg (fun f ↦ f w) hh
          change totalCoordinate K n t₀ ((K.total (.up ℕ)).d (n - 1) n b) =
            (K.X k).d q (q + 1) w at hb
          rw [hb, hw, sub_self]
      obtain ⟨a, ha⟩ := ih z' hdz' hsup
      refine ⟨a + b, ?_⟩
      rw [map_add, ha]
      exact sub_add_cancel _ _
  exact Nat.decreasingInduction (motive := fun k _ ↦ P k) step base
    (Nat.zero_le (n + 1)) x hx (fun s hs ↦ by omega)

/-- Acyclic rows imply acyclicity of the native first-quadrant total complex. -/
theorem acyclic_total_of_rowwise_exact (hK : ∀ p q, (K.X p).ExactAt q) :
    (K.total (.up ℕ)).Acyclic := by
  intro n
  rw [(K.total (.up ℕ)).exactAt_iff' (n - 1) n (n + 1) (by
    cases n with
    | zero => exact (ComplexShape.up ℕ).prev_eq_self' 0 (by intro i; change ¬i + 1 = 0; omega)
    | succ n => exact (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from
      rfl))
    ((ComplexShape.up ℕ).next_eq' rfl)]
  exact (ShortComplex.moduleCat_exact_iff _).mpr (total_cycle_boundary_of_rowwise_exact K hK n)

end HomologicalComplex₂

namespace HomologicalComplex₂
variable {R : Type u} [Ring R]

private theorem homologyπ_zero_iff (S : ShortComplex (ModuleCat.{v} R)) (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ x : S.X₁, S.f x = S.iCycles z := by
  have he : S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) :=
    congrArg (fun f => f z) S.homology_π_ι
  constructor
  · intro hz
    apply (S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles z)).mp
    rw [← he, hz, map_zero]
  · intro hz
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [map_zero, he]
    exact (S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles z)).mpr hz

/-- Injectivity on homology expressed using the original elements and differential. -/
theorem quasiIso_cycle_boundary {S T : ShortComplex (ModuleCat.{v} R)}
    (φ : S ⟶ T) [ShortComplex.QuasiIso φ]
    (x : S.X₂) (hx : S.g x = 0) (y : T.X₁) (hy : T.f y = φ.τ₂ x) :
    ∃ z : S.X₁, S.f z = x := by
  let z := S.cyclesMk x hx
  have hz : S.iCycles z = x := S.i_cyclesMk x hx
  have hz' : T.iCycles (ShortComplex.cyclesMap φ z) = φ.τ₂ x := by
    have hh := congrArg (fun f ↦ f z) (ShortComplex.cyclesMap_i φ)
    exact hh.trans (congrArg φ.τ₂ hz)
  have hb : T.homologyπ (ShortComplex.cyclesMap φ z) = 0 :=
    (homologyπ_zero_iff T _).mpr ⟨y, hy.trans hz'.symm⟩
  have hn := congrArg (fun f ↦ f z) (ShortComplex.homologyπ_naturality φ)
  change ShortComplex.homologyMap φ (S.homologyπ z) =
    T.homologyπ (ShortComplex.cyclesMap φ z) at hn
  have hc : S.homologyπ z = 0 := by
    apply (ModuleCat.mono_iff_injective (ShortComplex.homologyMap φ)).mp inferInstance
    simpa only [map_zero] using hn.trans hb
  obtain ⟨a,ha⟩ := (homologyπ_zero_iff S z).mp hc
  exact ⟨a,ha.trans hz⟩

/-- Surjectivity on homology expressed by an actual cycle and an actual boundary. -/
theorem quasiIso_cycle_lift {S T : ShortComplex (ModuleCat.{v} R)}
    (φ : S ⟶ T) [ShortComplex.QuasiIso φ]
    (y : T.X₂) (hy : T.g y = 0) :
    ∃ x : S.X₂, S.g x = 0 ∧ ∃ b : T.X₁, φ.τ₂ x - T.f b = y := by
  let z := T.cyclesMk y hy
  have hz : T.iCycles z = y := T.i_cyclesMk y hy
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (ShortComplex.homologyMap φ)).mp
    inferInstance (T.homologyπ z)
  obtain ⟨w,rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance a
  have hn := congrArg (fun f ↦ f w) (ShortComplex.homologyπ_naturality φ)
  change (ShortComplex.homologyMap φ) (S.homologyπ w) =
    T.homologyπ (ShortComplex.cyclesMap φ w) at hn
  have he : T.homologyπ (ShortComplex.cyclesMap φ w - z) = 0 := by
    rw [map_sub, ← hn, ha, sub_self]
  obtain ⟨b,hb⟩ := (homologyπ_zero_iff T _).mp he
  refine ⟨S.iCycles w, ?_, b, ?_⟩
  · exact congrArg (fun f ↦ f w) S.iCycles_g
  · have hi := congrArg (fun f ↦ f w) (ShortComplex.cyclesMap_i φ)
    change T.iCycles (ShortComplex.cyclesMap φ w) = φ.τ₂ (S.iCycles w) at hi
    rw [map_sub, hi, hz] at hb
    rw [hb]
    abel

/-- The elementary acyclicity equation for the mapping fiber of a quasi-isomorphism. -/
theorem quasiIso_fiber_lift {B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (φ : B ⟶ C) [QuasiIso φ] (q : ℕ)
    (x : B.X (q + 1)) (hx : B.d (q + 1) (q + 2) x = 0)
    (y : C.X q) (hy : C.d q (q + 1) y = φ.f (q + 1) x) :
    ∃ a : B.X q, B.d q (q + 1) a = x ∧
      ∃ b : C.X (q - 1), φ.f q a - C.d (q - 1) q b = y := by
  let φ₁ := (shortComplexFunctor' (ModuleCat.{v} R) (.up ℕ) q (q + 1) (q + 2)).map φ
  have : ShortComplex.QuasiIso φ₁ :=
    (quasiIsoAt_iff' φ q (q + 1) (q + 2)
      ((ComplexShape.up ℕ).prev_eq' rfl) ((ComplexShape.up ℕ).next_eq' rfl)).mp inferInstance
  obtain ⟨a,ha⟩ : ∃ a : B.X q, B.d q (q + 1) a = x :=
    quasiIso_cycle_boundary φ₁ x hx y hy
  have hz : C.d q (q + 1) (y - φ.f q a) = 0 := by
    have hc := congrArg (fun f ↦ f a) (φ.comm q (q + 1))
    change C.d q (q + 1) (φ.f q a) = φ.f (q + 1) (B.d q (q + 1) a) at hc
    rw [map_sub, hy, hc, ha, sub_self]
  let φ₀ := (shortComplexFunctor' (ModuleCat.{v} R) (.up ℕ) (q - 1) q (q + 1)).map φ
  have : ShortComplex.QuasiIso φ₀ :=
    (quasiIsoAt_iff' φ (q - 1) q (q + 1) (by
      cases q with
      | zero => exact (ComplexShape.up ℕ).prev_eq_self' 0 (by intro i; change ¬i + 1 = 0; omega)
      | succ q => exact (ComplexShape.up ℕ).prev_eq' rfl)
      ((ComplexShape.up ℕ).next_eq' rfl)).mp inferInstance
  obtain ⟨c,hc,b,hb⟩ : ∃ c : B.X q, B.d q (q + 1) c = 0 ∧
      ∃ b : C.X (q - 1), φ.f q c - C.d (q - 1) q b = y - φ.f q a :=
    quasiIso_cycle_lift φ₀ (y - φ.f q a) hz
  refine ⟨a + c, ?_, b, ?_⟩
  · change B.d q (q + 1) c = 0 at hc
    change B.d q (q + 1) a = x at ha
    rw [map_add, ha, hc, add_zero]
  · change φ.f q c - C.d (q - 1) q b = y - φ.f q a at hb
    rw [map_add]
    rw [add_sub_assoc, hb]
    abel

variable {B C : FirstQuadrant.{u, v} R}

@[reassoc]
theorem totalSummand_map (φ : B ⟶ C) (n : ℕ) (s : TotalDegree n) :
    totalSummand B n s ≫ (HomologicalComplex₂.total.map φ (.up ℕ)).f n =
      (φ.f s.val.1).f s.val.2 ≫ totalSummand C n s :=
  B.ιTotal_map C φ (.up ℕ) s.val.1 s.val.2 n s.property

@[reassoc]
theorem totalMap_coordinate (φ : B ⟶ C) (n : ℕ) (s : TotalDegree n) :
    (HomologicalComplex₂.total.map φ (.up ℕ)).f n ≫ totalCoordinate C n s =
      totalCoordinate B n s ≫ (φ.f s.val.1).f s.val.2 := by
  classical
  apply Sigma.hom_ext
  intro t
  change totalSummand B n t ≫ _ = totalSummand B n t ≫ _
  rw [totalSummand_map_assoc]
  by_cases ht : t = s
  · subst t
    simp
  · rw [totalSummand_coordinate_ne_assoc B n t s ht,
      totalSummand_coordinate_ne C n t s ht, comp_zero, zero_comp]

namespace TotalSupportedFrom
variable {K : FirstQuadrant.{u, v} R} {n k : ℕ} {x y : (K.total (.up ℕ)).X n}

theorem add (hx : TotalSupportedFrom K n k x) (hy : TotalSupportedFrom K n k y) :
    TotalSupportedFrom K n k (x + y) := by
  intro s hs
  rw [map_add, hx s hs, hy s hs, add_zero]

theorem sub (hx : TotalSupportedFrom K n k x) (hy : TotalSupportedFrom K n k y) :
    TotalSupportedFrom K n k (x - y) := by
  intro s hs
  rw [map_sub, hx s hs, hy s hs, sub_self]

theorem smul (e : ℤˣ) (hx : TotalSupportedFrom K n k x) :
    TotalSupportedFrom K n k (e • x) := by
  intro s hs
  change totalCoordinate K n s ((e : ℤ) • x) = 0
  rw [map_zsmul, hx s hs, smul_zero]

theorem zero : TotalSupportedFrom K n k 0 := fun _ _ ↦ map_zero _

theorem succ (hx : TotalSupportedFrom K n k x)
    (h : ∀ s : TotalDegree n, s.val.1 = k → totalCoordinate K n s x = 0) :
    TotalSupportedFrom K n (k + 1) x := by
  intro s hs
  rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs|hs
  · exact hx s hs
  · exact h s hs

theorem eq_zero (hx : TotalSupportedFrom K n (n + 1) x) : x = 0 := by
  apply totalCoordinate_ext K n
  intro s
  rw [map_zero]
  apply hx s
  have hh : s.val.1 + s.val.2 = n := s.property
  omega

end TotalSupportedFrom

theorem totalSummand_supported (K : FirstQuadrant.{u, v} R) (n : ℕ) (s : TotalDegree n)
    (w : (K.X s.val.1).X s.val.2) :
    TotalSupportedFrom K n s.val.1 (totalSummand K n s w) := by
  intro t ht
  have hst : s≠t := by intro h; subst t; omega
  exact congrArg (fun f ↦ f w) (totalSummand_coordinate_ne K n s t hst)

theorem total_d_summand_supported (K : FirstQuadrant.{u, v} R) (n m : ℕ) (hm : n + 1 = m)
    (s : TotalDegree n) (w : (K.X s.val.1).X s.val.2) :
    TotalSupportedFrom K m s.val.1 ((K.total (.up ℕ)).d n m (totalSummand K n s w)) := by
  intro t ht
  exact congrArg (fun f ↦ f w) (totalSummand_d_coordinate_eq_zero' K n m hm s t
    (by omega) (by omega))

theorem total_map_supported (φ : B ⟶ C) (n k : ℕ) (x : (B.total (.up ℕ)).X n)
    (hx : TotalSupportedFrom B n k x) :
    TotalSupportedFrom C n k ((HomologicalComplex₂.total.map φ (.up ℕ)).f n x) := by
  intro s hs
  have hh := congrArg (fun f ↦ f x) (totalMap_coordinate φ n s)
  change totalCoordinate C n s ((HomologicalComplex₂.total.map φ (.up ℕ)).f n x) =
    (φ.f s.val.1).f s.val.2 (totalCoordinate B n s x) at hh
  rw [hh, hx s hs, map_zero]

/-- Elementwise cycle and boundary lifting characterize quasi-isomorphisms of short complexes. -/
theorem quasiIso_of_cycle_lifts {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g x = 0 → ∀ y : T.X₁, T.f y = φ.τ₂ x →
      ∃ a : S.X₁, S.f a = x)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ b : T.X₁, φ.τ₂ x - T.f b = y) :
    ShortComplex.QuasiIso φ := by
  rw [ShortComplex.quasiIso_iff]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero (ShortComplex.homologyMap φ).hom).mpr
    intro a ha
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance a
    have hn := congrArg (fun f ↦ f z) (ShortComplex.homologyπ_naturality φ)
    change ShortComplex.homologyMap φ (S.homologyπ z) =
      T.homologyπ (ShortComplex.cyclesMap φ z) at hn
    obtain ⟨y,hy⟩ := (homologyπ_zero_iff T _).mp (hn.symm.trans ha)
    have hi := congrArg (fun f ↦ f z) (ShortComplex.cyclesMap_i φ)
    change T.iCycles (ShortComplex.cyclesMap φ z) = φ.τ₂ (S.iCycles z) at hi
    have hz : S.g (S.iCycles z) = 0 := congrArg (fun f ↦ f z) S.iCycles_g
    obtain ⟨x,hx⟩ := hinj (S.iCycles z) hz y (hy.trans hi)
    exact (homologyπ_zero_iff S z).mpr ⟨x,hx⟩
  · intro a
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance a
    have hz : T.g (T.iCycles z) = 0 := congrArg (fun f ↦ f z) T.iCycles_g
    obtain ⟨x,hx,b,hb⟩ := hsurj (T.iCycles z) hz
    let w := S.cyclesMk x hx
    have hw : S.iCycles w = x := S.i_cyclesMk x hx
    refine ⟨S.homologyπ w, ?_⟩
    have hn := congrArg (fun f ↦ f w) (ShortComplex.homologyπ_naturality φ)
    change ShortComplex.homologyMap φ (S.homologyπ w) =
      T.homologyπ (ShortComplex.cyclesMap φ w) at hn
    rw [hn]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (homologyπ_zero_iff T _).mpr
    refine ⟨b, ?_⟩
    have hi := congrArg (fun f ↦ f w) (ShortComplex.cyclesMap_i φ)
    change T.iCycles (ShortComplex.cyclesMap φ w) = φ.τ₂ (S.iCycles w) at hi
    rw [map_sub, hi, hw]
    rw [sub_eq_iff_eq_add.mp hb]
    abel

/-- The degree-zero injectivity equation has no incoming boundary term. -/
theorem quasiIso_cycle_zero_at_zero {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (φ : K ⟶ L) [QuasiIso φ] (x : K.X 0)
    (hx : K.d 0 1 x = 0) (hφx : φ.f 0 x = 0) : x = 0 := by
  let ψ := (shortComplexFunctor' (ModuleCat.{v} R) (.up ℕ) 0 0 1).map φ
  have : ShortComplex.QuasiIso ψ := (CochainComplex.quasiIsoAt₀_iff φ).mp inferInstance
  obtain ⟨a,ha⟩ : ∃ a : K.X 0, K.d 0 0 a = x :=
    quasiIso_cycle_boundary ψ x hx 0 (by
      change L.d 0 0 0 = φ.f 0 x
      rw [map_zero,hφx])
  rw [K.shape 0 0 (by simp)] at ha
  exact ha.symm

/-- Fiber lifting in positive degrees, together with degree-zero injectivity,
proves quasi-isomorphism of the original cochain map. -/
theorem quasiIso_of_fiber_lifts {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (φ : K ⟶ L)
    (h₀ : ∀ x : K.X 0, K.d 0 1 x = 0 → φ.f 0 x = 0 → x = 0)
    (h : ∀ n (x : K.X (n + 1)), K.d (n + 1) (n + 2) x = 0 →
      ∀ y : L.X n, L.d n (n + 1) y = φ.f (n + 1) x →
      ∃ a : K.X n, K.d n (n + 1) a = x ∧
        ∃ b : L.X (n - 1), φ.f n a - L.d (n - 1) n b = y) : QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' φ (n - 1) n (n + 1) (by
    cases n with
    | zero => exact (ComplexShape.up ℕ).prev_eq_self' 0 (by intro i; change ¬i + 1 = 0; omega)
    | succ n => exact (ComplexShape.up ℕ).prev_eq' rfl)
    ((ComplexShape.up ℕ).next_eq' rfl)]
  apply quasiIso_of_cycle_lifts
  · change ∀ x : K.X n, K.d n (n + 1) x = 0 → ∀ y : L.X (n - 1),
      L.d (n - 1) n y = φ.f n x → ∃ a : K.X (n - 1), K.d (n - 1) n a = x
    intro x hx y hy
    cases n with
    | zero =>
      have hφx : φ.f 0 x = 0 := by
        rw [L.shape 0 0 (by simp)] at hy
        exact hy.symm
      exact ⟨0, (map_zero _).trans (h₀ x hx hφx).symm⟩
    | succ n =>
      obtain ⟨a,ha,_,_⟩ := h n x hx y hy
      exact ⟨a,ha⟩
  · change ∀ y : L.X n, L.d n (n + 1) y = 0 →
      ∃ x : K.X n, K.d n (n + 1) x = 0 ∧ ∃ b : L.X (n - 1), φ.f n x - L.d (n - 1) n b = y
    intro y hy
    exact h n 0 (map_zero _) y (by rw [hy,map_zero])

/-- A row boundary lifts to a total boundary supported in the same or higher outer degrees. -/
theorem total_row_boundary_lift (K : FirstQuadrant.{u, v} R) (n k q : ℕ) (hq : k + q = n)
    (v : (K.X k).X (q - 1)) :
    ∃ b : (K.total (.up ℕ)).X (n - 1),
      TotalSupportedFrom K n k ((K.total (.up ℕ)).d (n - 1) n b) ∧
      totalCoordinate K n ⟨(k,q),hq⟩ ((K.total (.up ℕ)).d (n - 1) n b) =
        (-1 : ℤˣ)^k • (K.X k).d (q - 1) q v := by
  cases q with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · rw [map_zero]
      exact TotalSupportedFrom.zero
    · rw [map_zero,map_zero,(K.X k).shape 0 0 (by simp)]
      exact (smul_zero _).symm
  | succ q =>
    let r : TotalDegree (n - 1) := ⟨(k,q),by change k + q = n - 1; omega⟩
    have hn : n - 1 + 1 = n := by omega
    refine ⟨totalSummand K (n - 1) r v,
      total_d_summand_supported K (n - 1) n hn r v, ?_⟩
    have hh := totalSummand_d_coordinate_vertical' K (n - 1) n k q r.property hn
    exact congrArg (fun a ↦ a v) hh

/-- Elementwise lifting in the total mapping fiber, proved by finite antidiagonal elimination. -/
theorem total_fiber_lift (φ : B ⟶ C) (hφ : ∀ p, QuasiIso (φ.f p)) (n : ℕ)
    (x : (B.total (.up ℕ)).X (n + 1)) (hx : (B.total (.up ℕ)).d (n + 1) (n + 2) x = 0)
    (y : (C.total (.up ℕ)).X n)
    (hy : (C.total (.up ℕ)).d n (n + 1) y =
      (HomologicalComplex₂.total.map φ (.up ℕ)).f (n + 1) x) :
    ∃ a : (B.total (.up ℕ)).X n, (B.total (.up ℕ)).d n (n + 1) a = x ∧
      ∃ b : (C.total (.up ℕ)).X (n - 1),
        (HomologicalComplex₂.total.map φ (.up ℕ)).f n a - (C.total (.up ℕ)).d (n - 1) n b = y := by
  classical
  let f := HomologicalComplex₂.total.map φ (.up ℕ)
  let P (k : ℕ) := ∀ x : (B.total (.up ℕ)).X (n + 1),
    (B.total (.up ℕ)).d (n + 1) (n + 2) x = 0 → ∀ y : (C.total (.up ℕ)).X n,
    (C.total (.up ℕ)).d n (n + 1) y = f.f (n + 1) x →
    TotalSupportedFrom B (n + 1) k x → TotalSupportedFrom C n k y →
    ∃ a : (B.total (.up ℕ)).X n, (B.total (.up ℕ)).d n (n + 1) a = x ∧
      ∃ b : (C.total (.up ℕ)).X (n - 1), f.f n a - (C.total (.up ℕ)).d (n - 1) n b = y
  have base : P (n + 2) := by
    intro x _ y _ hsx hsy
    have hyy : y = 0 := TotalSupportedFrom.eq_zero (fun s hs ↦ hsy s (by omega))
    exact ⟨0, (map_zero _).trans hsx.eq_zero.symm, 0, by simp [hyy]⟩
  have step : ∀ k, k<n + 2 → P (k + 1) → P k := by
    intro k hk ih x hx y hy hsx hsy
    have : QuasiIso (φ.f k) := hφ k
    by_cases hkn : k = n + 1
    · subst k
      have hyy : y = 0 := hsy.eq_zero
      let t : TotalDegree (n + 1) := ⟨(n + 1,0), Nat.add_zero _⟩
      have hxc : (B.X (n + 1)).d 0 1 (totalCoordinate B (n + 1) t x) = 0 := by
        have hh := totalCoordinate_d_of_support B (n + 1) (n + 1) 0 (Nat.add_zero _) x hsx
        rw [hx,map_zero] at hh
        change (0 : (B.X (n + 1)).X 1) = (-1 : ℤˣ)^(n + 1) •
          (B.X (n + 1)).d 0 1 (totalCoordinate B (n + 1) t x) at hh
        exact (smul_eq_zero_iff_eq _).mp hh.symm
      have hxf : (φ.f (n + 1)).f 0 (totalCoordinate B (n + 1) t x) = 0 := by
        have hm := congrArg (fun a ↦ a x) (totalMap_coordinate φ (n + 1) t)
        change totalCoordinate C (n + 1) t (f.f (n + 1) x) =
          (φ.f (n + 1)).f 0 (totalCoordinate B (n + 1) t x) at hm
        rw [← hm, ← hy, hyy, map_zero, map_zero]
      have hxx : totalCoordinate B (n + 1) t x = 0 :=
        quasiIso_cycle_zero_at_zero (φ.f (n + 1)) _ hxc hxf
      apply ih x hx y hy
      · apply hsx.succ
        intro s hs
        have he : s = t := by
          apply Subtype.ext
          apply Prod.ext hs
          have hh : s.val.1 + s.val.2 = n + 1 := s.property
          dsimp [t]
          omega
        rw [he]
        exact hxx
      · intro s hs
        rw [hyy,map_zero]
    · have hkn' : k≤n := by omega
      let q := n - k
      have hq : k + q = n := by dsimp [q]; omega
      let s : TotalDegree n := ⟨(k,q),hq⟩
      let t : TotalDegree (n + 1) := ⟨(k,q + 1),by change k + (q + 1) = n + 1; omega⟩
      let e : ℤˣ := (-1)^k
      let xc := totalCoordinate B (n + 1) t x
      let yc := totalCoordinate C n s y
      have hxc : (B.X k).d (q + 1) (q + 2) xc = 0 := by
        have hh := totalCoordinate_d_of_support B (n + 1) k (q + 1) t.property x hsx
        rw [hx,map_zero] at hh
        change (0 : (B.X k).X (q + 2)) = e • (B.X k).d (q + 1) (q + 2) xc at hh
        exact (smul_eq_zero_iff_eq e).mp hh.symm
      have hyc : (C.X k).d q (q + 1) (e • yc) = (φ.f k).f (q + 1) xc := by
        have hd := totalCoordinate_d_of_support C n k q hq y hsy
        have hm := congrArg (fun a ↦ a x) (totalMap_coordinate φ (n + 1) t)
        change totalCoordinate C (n + 1) t (f.f (n + 1) x) = (φ.f k).f (q + 1) xc at hm
        change totalCoordinate C (n + 1) t ((C.total (.up ℕ)).d n (n + 1) y) =
          e • (C.X k).d q (q + 1) yc at hd
        change (C.X k).d q (q + 1) ((e : ℤ) • yc) = _
        rw [map_zsmul]
        exact hd.symm.trans ((congrArg (totalCoordinate C (n + 1) t) hy).trans hm)
      obtain ⟨u,hu,v,hv⟩ := quasiIso_fiber_lift (φ.f k) q xc hxc (e • yc) hyc
      let a : (B.total (.up ℕ)).X n := (e • totalSummand B n s) u
      have has : TotalSupportedFrom B n k a := (totalSummand_supported B n s u).smul e
      have hads : TotalSupportedFrom B (n + 1) k ((B.total (.up ℕ)).d n (n + 1) a) := by
        have hh := (total_d_summand_supported B n (n + 1) rfl s u).smul e
        change TotalSupportedFrom B (n + 1) k
          ((e : ℤ) • (B.total (.up ℕ)).d n (n + 1) (totalSummand B n s u)) at hh
        change TotalSupportedFrom B (n + 1) k
          ((B.total (.up ℕ)).d n (n + 1) ((e : ℤ) • totalSummand B n s u))
        rwa [map_zsmul]
      have had : totalCoordinate B (n + 1) t ((B.total (.up ℕ)).d n (n + 1) a) = xc := by
        have hh : (e • totalSummand B n s) ≫ (B.total (.up ℕ)).d n (n + 1) ≫
            totalCoordinate B (n + 1) t = (B.X k).d q (q + 1) := by
          rw [Linear.units_smul_comp]
          have hm := totalSummand_d_coordinate_vertical B n k q hq
          change totalSummand B n s ≫ _ ≫ totalCoordinate B (n + 1) t = _ at hm
          rw [hm]
          change e • (e • (B.X k).d q (q + 1)) = _
          rw [smul_smul, Int.units_mul_self, one_smul]
        exact (congrArg (fun a ↦ a u) hh).trans hu
      have haf : totalCoordinate C n s (f.f n a) = e • (φ.f k).f q u := by
        have hh : (e • totalSummand B n s) ≫ f.f n ≫ totalCoordinate C n s =
            e • (φ.f k).f q := by
          rw [Linear.units_smul_comp, totalSummand_map_assoc,
            totalSummand_coordinate_self, Category.comp_id]
        exact congrArg (fun a ↦ a u) hh
      obtain ⟨b,hbs,hb⟩ : ∃ b : (C.total (.up ℕ)).X (n - 1),
          TotalSupportedFrom C n k ((C.total (.up ℕ)).d (n - 1) n b) ∧
          totalCoordinate C n s ((C.total (.up ℕ)).d (n - 1) n b) =
            e • (C.X k).d (q - 1) q v := by
        exact total_row_boundary_lift C n k q hq v
      let x' := x - (B.total (.up ℕ)).d n (n + 1) a
      let y' := y - f.f n a + (C.total (.up ℕ)).d (n - 1) n b
      have hx' : (B.total (.up ℕ)).d (n + 1) (n + 2) x' = 0 := by
        have hh := congrArg (fun a' ↦ a' a) ((B.total (.up ℕ)).d_comp_d n (n + 1) (n + 2))
        change (B.total (.up ℕ)).d (n + 1) (n + 2) ((B.total (.up ℕ)).d n (n + 1) a) = 0 at hh
        dsimp [x']
        rw [map_sub,hx,hh,sub_zero]
      have hy' : (C.total (.up ℕ)).d n (n + 1) y' = f.f (n + 1) x' := by
        have hh := congrArg (fun a' ↦ a' b) ((C.total (.up ℕ)).d_comp_d (n - 1) n (n + 1))
        change (C.total (.up ℕ)).d n (n + 1) ((C.total (.up ℕ)).d (n - 1) n b) = 0 at hh
        have hc := congrArg (fun a' ↦ a' a) (f.comm n (n + 1))
        change (C.total (.up ℕ)).d n (n + 1) (f.f n a) =
          f.f (n + 1) ((B.total (.up ℕ)).d n (n + 1) a) at hc
        dsimp [y',x']
        rw [map_add,map_sub,hy,hc,hh,add_zero,map_sub]
      have hsx' : TotalSupportedFrom B (n + 1) (k + 1) x' := by
        apply (hsx.sub hads).succ
        intro r hr
        have he : r = t := by
          apply Subtype.ext
          apply Prod.ext hr
          have hh : r.val.1 + r.val.2 = n + 1 := r.property
          dsimp [t]
          omega
        subst r
        change totalCoordinate B (n + 1) t (x - _) = 0
        rw [map_sub,had]
        exact sub_self _
      have hsy' : TotalSupportedFrom C n (k + 1) y' := by
        apply ((hsy.sub (total_map_supported φ n k a has)).add hbs).succ
        intro r hr
        have he : r = s := by
          apply Subtype.ext
          apply Prod.ext hr
          have hh : r.val.1 + r.val.2 = n := r.property
          dsimp [s]
          omega
        subst r
        change totalCoordinate C n s (y - f.f n a + (C.total (.up ℕ)).d (n - 1) n b) = 0
        rw [map_add,map_sub,haf,hb]
        have hv' := congrArg (fun z ↦ e • z) hv
        rw [smul_sub,smul_smul,Int.units_mul_self,one_smul] at hv'
        change yc - e • (φ.f k).f q u + e • (C.X k).d (q - 1) q v = 0
        rw [← hv']
        abel
      obtain ⟨a',ha',b',hb'⟩ := ih x' hx' y' hy' hsx' hsy'
      refine ⟨a'+a, ?_, b'+b, ?_⟩
      · rw [map_add,ha']
        exact sub_add_cancel _ _
      · rw [map_add,map_add]
        have hh : f.f n a' - (C.total (.up ℕ)).d (n - 1) n b' =
            y - f.f n a + (C.total (.up ℕ)).d (n - 1) n b := hb'
        calc
          _ = (f.f n a' - (C.total (.up ℕ)).d (n - 1) n b') +
            f.f n a - (C.total (.up ℕ)).d (n - 1) n b := by abel
          _ = y := by rw [hh]; abel
  exact Nat.decreasingInduction (motive := fun k _ ↦ P k) step base (Nat.zero_le (n + 2))
    x hx y hy (fun s hs ↦ by omega) (fun s hs ↦ by omega)

/-- Degree-zero injectivity of the total map follows from the degree-zero row comparison. -/
theorem total_cycle_zero_at_zero (φ : B ⟶ C) (hφ : ∀ p, QuasiIso (φ.f p))
    (x : (B.total (.up ℕ)).X 0) (hx : (B.total (.up ℕ)).d 0 1 x = 0)
    (hfx : (HomologicalComplex₂.total.map φ (.up ℕ)).f 0 x = 0) : x = 0 := by
  have : QuasiIso (φ.f 0) := hφ 0
  let s : TotalDegree 0 := ⟨(0,0), rfl⟩
  have hxc : (B.X 0).d 0 1 (totalCoordinate B 0 s x) = 0 := by
    have hh := totalCoordinate_d_of_support B 0 0 0 rfl x (fun s hs ↦ by omega)
    rw [hx,map_zero] at hh
    simpa only [pow_zero,one_smul] using hh.symm
  have hxf : (φ.f 0).f 0 (totalCoordinate B 0 s x) = 0 := by
    have hh := congrArg (fun a ↦ a x) (totalMap_coordinate φ 0 s)
    change totalCoordinate C 0 s ((HomologicalComplex₂.total.map φ (.up ℕ)).f 0 x) =
      (φ.f 0).f 0 (totalCoordinate B 0 s x) at hh
    rw [← hh,hfx,map_zero]
  have hxx := quasiIso_cycle_zero_at_zero (φ.f 0) _ hxc hxf
  apply totalCoordinate_ext B 0
  intro t
  have he : t = s := by
    apply Subtype.ext
    have hh : t.val.1 + t.val.2 = 0 := t.property
    apply Prod.ext <;> dsimp [s] <;> omega
  rw [he,map_zero]
  exact hxx

/-- Rowwise quasi-isomorphisms induce a quasi-isomorphism of the native first-quadrant total.
This holds for modules over every ring; the modules need not be finite dimensional or split. -/
theorem quasiIso_total_of_rowwise (φ : B ⟶ C) (hφ : ∀ p, QuasiIso (φ.f p)) :
    QuasiIso (HomologicalComplex₂.total.map φ (.up ℕ)) :=
  quasiIso_of_fiber_lifts (HomologicalComplex₂.total.map φ (.up ℕ))
    (total_cycle_zero_at_zero φ hφ) (total_fiber_lift φ hφ)

/-- A rowwise quasi-isomorphic augmentation gives the actual canonical total quasi-isomorphism. -/
theorem quasiIso_totalAugmentation {L : CochainComplex (ModuleCat.{v} R) ℕ}
    {B : FirstQuadrant.{u, v} R} (α : (SingleSecondZero.{u, v} R).obj L ⟶ B)
    (hα : ∀ p, QuasiIso (α.f p)) : QuasiIso (totalAugmentation α) := by
  have : QuasiIso (HomologicalComplex₂.total.map α (.up ℕ)) :=
    quasiIso_total_of_rowwise α hα
  change QuasiIso ((singleSecondZeroTotalIso L).hom ≫
    HomologicalComplex₂.total.map α (.up ℕ))
  infer_instance

/-- The other-axis augmentation is a quasi-isomorphism after the actual signed flip. -/
theorem quasiIso_totalAugmentationFlip {L : CochainComplex (ModuleCat.{v} R) ℕ}
    {B : FirstQuadrant.{u, v} R} (α : (SingleSecondZero.{u, v} R).obj L ⟶ B.flip)
    (hα : ∀ p, QuasiIso (α.f p)) : QuasiIso (totalAugmentationFlip α) := by
  have : QuasiIso (totalAugmentation α) := quasiIso_totalAugmentation α hα
  change QuasiIso (totalAugmentation α ≫ (B.totalFlipIso (.up ℕ)).hom)
  infer_instance

end HomologicalComplex₂
