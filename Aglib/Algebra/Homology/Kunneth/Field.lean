/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Aglib.Algebra.Homology.TotalComplex.FirstQuadrant

/-!
# Canonical homology maps for the field Künneth construction

The tensor-of-cycles map must descend through the original homology
projections before any splitting is chosen. This file starts with the
canonical bilinear descent through native short-complex homology. The
construction is valid over a commutative ring and uses only the native
cokernel universal property; cycle lifts occur only in proofs that an
equation follows from its values on cycle classes.

The descended first-quadrant map is natural and preserves the original tensor
unit, associator, and Koszul symmetry. Over a field it is bijective. Its
bijectivity proof uses internal sections of the original homology projections
and the native rowwise-total quasi-isomorphism theorem, then identifies the
comparison with the already constructed canonical map on every tensor summand.
No splitting or replacement cohomology object enters the public equivalence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R]
  (S T : ShortComplex (ModuleCat.{v} R)) (M : ModuleCat.{v} R)

/-- The original homology projection is surjective on module elements. -/
theorem homologyπ_surjective : Function.Surjective S.homologyπ :=
  (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance

/-- The native homology descent takes an original cycle class to the
value of its original cycle map. -/
@[simp]
theorem descHomology_apply_homologyπ (f : S.cycles ⟶ M) (hf : S.toCycles ≫ f = 0)
    (x : S.cycles) :
    (S.descHomology f hf).hom (S.homologyπ x) = f x :=
  ConcreteCategory.congr_hom (S.π_descHomology f hf) x

/-- A bilinear map on the original cycles which kills a boundary in
either argument descends canonically to the original homology objects. -/
def homologyBilinearDesc
    (f : S.cycles →ₗ[R] T.cycles →ₗ[R] M)
    (hleft : S.toCycles ≫ ModuleCat.ofHom f = 0)
    (hright : ∀ x : S.cycles, T.toCycles ≫ ModuleCat.ofHom (f x) = 0) :
    S.homology →ₗ[R] T.homology →ₗ[R] M := by
  let F : S.homology →ₗ[R] (T.cycles →ₗ[R] M) :=
    (S.descHomology (ModuleCat.ofHom f) hleft).hom
  have hF (x : S.cycles) : F (S.homologyπ x) = f x :=
    descHomology_apply_homologyπ S _ (ModuleCat.ofHom f) hleft x
  have hFright (x : S.homology) : T.toCycles ≫ ModuleCat.ofHom (F x) = 0 := by
    obtain ⟨y, rfl⟩ := homologyπ_surjective S x
    rw [hF]
    exact hright y
  have hD (x : S.homology) (y : T.cycles) :
      (T.descHomology (ModuleCat.ofHom (F x)) (hFright x)).hom (T.homologyπ y) = F x y :=
    descHomology_apply_homologyπ T M (ModuleCat.ofHom (F x)) (hFright x) y
  refine {
    toFun := fun x => (T.descHomology (ModuleCat.ofHom (F x)) (hFright x)).hom
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := homologyπ_surjective T z
    simp only [LinearMap.add_apply]
    rw [hD, hD, hD]
    exact LinearMap.congr_fun (F.map_add x y) w
  · intro r x
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := homologyπ_surjective T z
    simp only [LinearMap.smul_apply, RingHom.id_apply]
    rw [hD, hD]
    exact LinearMap.congr_fun (F.map_smul r x) w

/-- The canonical bilinear descent has the original cycle-class formula. -/
@[simp]
theorem homologyBilinearDesc_apply_homologyπ
    (f : S.cycles →ₗ[R] T.cycles →ₗ[R] M)
    (hleft : S.toCycles ≫ ModuleCat.ofHom f = 0)
    (hright : ∀ x : S.cycles, T.toCycles ≫ ModuleCat.ofHom (f x) = 0)
    (x : S.cycles) (y : T.cycles) :
    homologyBilinearDesc S T M f hleft hright (S.homologyπ x) (T.homologyπ y) = f x y := by
  simp only [homologyBilinearDesc, LinearMap.coe_mk, AddHom.coe_mk,
    descHomology_apply_homologyπ]
  change ((S.descHomology (ModuleCat.ofHom f) hleft).hom (S.homologyπ x)) y = f x y
  exact congrArg (fun g : T.cycles →ₗ[R] M => g y)
    (descHomology_apply_homologyπ S _ (ModuleCat.ofHom f) hleft x)

/-- The original cycle-class formula uniquely determines the bilinear
homology map. No chosen cycle splitting enters the public construction. -/
theorem homologyBilinearDesc_unique
    (f : S.cycles →ₗ[R] T.cycles →ₗ[R] M)
    (hleft : S.toCycles ≫ ModuleCat.ofHom f = 0)
    (hright : ∀ x : S.cycles, T.toCycles ≫ ModuleCat.ofHom (f x) = 0)
    (g : S.homology →ₗ[R] T.homology →ₗ[R] M)
    (hg : ∀ x : S.cycles, ∀ y : T.cycles,
      g (S.homologyπ x) (T.homologyπ y) = f x y) :
    g = homologyBilinearDesc S T M f hleft hright := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := homologyπ_surjective S x
  obtain ⟨y, rfl⟩ := homologyπ_surjective T y
  rw [homologyBilinearDesc_apply_homologyπ]
  exact hg x y

/-- Naturality of the whole canonical bilinear homology descent follows
from the original compatibility square on cycles. -/
theorem homologyBilinearDesc_naturality
    (S' T' : ShortComplex (ModuleCat.{v} R)) (M' : ModuleCat.{v} R)
    (α : S ⟶ S') (β : T ⟶ T') (γ : M ⟶ M')
    (f : S.cycles →ₗ[R] T.cycles →ₗ[R] M)
    (hleft : S.toCycles ≫ ModuleCat.ofHom f = 0)
    (hright : ∀ x : S.cycles, T.toCycles ≫ ModuleCat.ofHom (f x) = 0)
    (f' : S'.cycles →ₗ[R] T'.cycles →ₗ[R] M')
    (hleft' : S'.toCycles ≫ ModuleCat.ofHom f' = 0)
    (hright' : ∀ x : S'.cycles, T'.toCycles ≫ ModuleCat.ofHom (f' x) = 0)
    (hf : ∀ x : S.cycles, ∀ y : T.cycles,
      γ (f x y) = f' (cyclesMap α x) (cyclesMap β y)) :
    (homologyBilinearDesc S T M f hleft hright).compr₂ γ.hom =
      (homologyBilinearDesc S' T' M' f' hleft' hright').compl₁₂
        (homologyMap α).hom (homologyMap β).hom := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := homologyπ_surjective S x
  obtain ⟨y, rfl⟩ := homologyπ_surjective T y
  change γ (homologyBilinearDesc S T M f hleft hright (S.homologyπ x) (T.homologyπ y)) =
    homologyBilinearDesc S' T' M' f' hleft' hright'
      (homologyMap α (S.homologyπ x)) (homologyMap β (T.homologyπ y))
  have hα : homologyMap α (S.homologyπ x) = S'.homologyπ (cyclesMap α x) :=
    ConcreteCategory.congr_hom (homologyπ_naturality α) x
  have hβ : homologyMap β (T.homologyπ y) = T'.homologyπ (cyclesMap β y) :=
    ConcreteCategory.congr_hom (homologyπ_naturality β) y
  rw [homologyBilinearDesc_apply_homologyπ, hα, hβ,
    homologyBilinearDesc_apply_homologyπ]
  exact hf x y

end CategoryTheory.ShortComplex

namespace HomologicalComplex.Kunneth

open MonoidalCategory BraidedCategory
open scoped TensorProduct

variable {R : Type u} [CommRing R]
  (K L : CochainComplex (ModuleCat.{u} R) ℕ)

/-- The original bifunctor bicomplex underlying the native tensor total.
This is an abbreviation for the same constructor used by `tensorObj`. -/
abbrev tensorBicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex (.up ℕ) (.up ℕ)).obj K).obj L

/-- The original homogeneous tensor inclusion has the native signed
Leibniz differential. No alternative total complex is introduced. -/
theorem tensorInclusion_d (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        (HomologicalComplex.tensorObj K L).d n (n + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
          HomologicalComplex.ιTensorObj K L (p + 1) q (n + 1) (by omega) +
        (-1 : ℤˣ) ^ p • ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
          HomologicalComplex.ιTensorObj K L p (q + 1) (n + 1) (by omega)) := by
  have h₁ : ((tensorBicomplex K L).d p (p + 1)).f q =
      K.d p (p + 1) ⊗ₘ 𝟙 (L.X q) := by
    change K.d p (p + 1) ▷ L.X q = _
    exact (MonoidalCategory.tensorHom_id _ _).symm
  have h₂ : ((tensorBicomplex K L).X p).d q (q + 1) =
      𝟙 (K.X p) ⊗ₘ L.d q (q + 1) := by
    change K.X p ◁ L.d q (q + 1) = _
    exact (MonoidalCategory.id_tensorHom _ _).symm
  simpa only [h₁, h₂] using (tensorBicomplex K L).totalSummand_d_up n p q h

/-- Tensor the original cycle inclusions and include the resulting
homogeneous tensor into the original total degree. -/
def tensorCyclesToTerm (p q n : ℕ) (h : p + q = n) :
    K.cycles p ⊗ L.cycles q ⟶ (HomologicalComplex.tensorObj K L).X n :=
  (K.iCycles p ⊗ₘ L.iCycles q) ≫ HomologicalComplex.ιTensorObj K L p q n h

/-- Tensor products of original cycles are original cycles of the
native tensor total, with its actual signed differential. -/
theorem tensorCyclesToTerm_d (p q n : ℕ) (h : p + q = n) :
    tensorCyclesToTerm K L p q n h ≫
      (HomologicalComplex.tensorObj K L).d n (n + 1) = 0 := by
  rw [tensorCyclesToTerm, Category.assoc, tensorInclusion_d,
    Preadditive.comp_add, Linear.comp_units_smul]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    HomologicalComplex.iCycles_d, Category.comp_id,
    MonoidalPreadditive.zero_tensor, MonoidalPreadditive.tensor_zero,
    zero_comp, smul_zero, add_zero]

/-- The canonical lift of the original tensor-of-cycles map into the
original cycle object of the native total. -/
def tensorCyclesToCycles (p q n : ℕ) (h : p + q = n) :
    K.cycles p ⊗ L.cycles q ⟶ (HomologicalComplex.tensorObj K L).cycles n :=
  (HomologicalComplex.tensorObj K L).liftCycles
    (tensorCyclesToTerm K L p q n h) (n + 1) (by simp)
    (tensorCyclesToTerm_d K L p q n h)

/-- The cycle lift has exactly the original tensor inclusion as its
underlying term map. -/
@[reassoc (attr := simp)]
theorem tensorCyclesToCycles_iCycles (p q n : ℕ) (h : p + q = n) :
    tensorCyclesToCycles K L p q n h ≫ (HomologicalComplex.tensorObj K L).iCycles n =
      tensorCyclesToTerm K L p q n h :=
  (HomologicalComplex.tensorObj K L).liftCycles_i _ _ _ _

/-- The canonical bilinear pairing of original cycles with values in
the original homology of the native tensor total. -/
def tensorCyclesPairing (p q n : ℕ) (h : p + q = n) :
    K.cycles p →ₗ[R] L.cycles q →ₗ[R] (HomologicalComplex.tensorObj K L).homology n :=
  TensorProduct.curry
    (tensorCyclesToCycles K L p q n h ≫ (HomologicalComplex.tensorObj K L).homologyπ n).hom

/-- The pairing is the class of the original tensor of cycles. -/
theorem tensorCyclesPairing_apply (p q n : ℕ) (h : p + q = n)
    (x : K.cycles p) (y : L.cycles q) :
    tensorCyclesPairing K L p q n h x y =
      (HomologicalComplex.tensorObj K L).homologyπ n
        (tensorCyclesToCycles K L p q n h (x ⊗ₜ[R] y)) := rfl

/-- A map to the original cycles has zero homology class when its
original term map factors through a differential. -/
theorem cycles_homologyπ_eq_zero_of_boundary
    {Z : ModuleCat.{u} R} {i n : ℕ} (a : Z ⟶ K.cycles n) (b : Z ⟶ K.X i)
    (h : a ≫ K.iCycles n = b ≫ K.d i n) : a ≫ K.homologyπ n = 0 := by
  have ha : a = b ≫ K.toCycles i n := by
    apply (cancel_mono (K.iCycles n)).mp
    rw [Category.assoc, HomologicalComplex.toCycles_i]
    exact h
  rw [ha, Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

/-- A boundary in the first factor gives a boundary in the original
tensor total, against any cycle in the second factor. -/
theorem tensorCyclesToCycles_left_boundary (i p q n : ℕ)
    (hi : i + 1 = p) (h : p + q = n) :
    (K.toCycles i p ⊗ₘ 𝟙 (L.cycles q)) ≫ tensorCyclesToCycles K L p q n h ≫
      (HomologicalComplex.tensorObj K L).homologyπ n = 0 := by
  subst p
  have hn : n = i + q + 1 := by omega
  rcases hn with rfl
  apply cycles_homologyπ_eq_zero_of_boundary (HomologicalComplex.tensorObj K L)
    ((K.toCycles i (i + 1) ⊗ₘ 𝟙 (L.cycles q)) ≫
      tensorCyclesToCycles K L (i + 1) q (i + q + 1) h)
    ((𝟙 (K.X i) ⊗ₘ L.iCycles q) ≫ HomologicalComplex.ιTensorObj K L i q (i + q) rfl)
  simp only [Category.assoc, tensorCyclesToCycles_iCycles]
  rw [tensorCyclesToTerm, tensorInclusion_d,
    Preadditive.comp_add, Linear.comp_units_smul]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d,
    Category.id_comp, Category.comp_id, MonoidalPreadditive.tensor_zero,
    zero_comp, smul_zero, add_zero]

/-- A boundary in the second factor gives a boundary in the original
tensor total. The native sign is its own inverse, including in characteristic two. -/
theorem tensorCyclesToCycles_right_boundary (p j q n : ℕ)
    (hj : j + 1 = q) (h : p + q = n) :
    (𝟙 (K.cycles p) ⊗ₘ L.toCycles j q) ≫ tensorCyclesToCycles K L p q n h ≫
      (HomologicalComplex.tensorObj K L).homologyπ n = 0 := by
  subst q
  have hn : n = p + j + 1 := by omega
  rcases hn with rfl
  apply cycles_homologyπ_eq_zero_of_boundary (HomologicalComplex.tensorObj K L)
    ((𝟙 (K.cycles p) ⊗ₘ L.toCycles j (j + 1)) ≫
      tensorCyclesToCycles K L p (j + 1) (p + j + 1) h)
    ((-1 : ℤˣ) ^ p • ((K.iCycles p ⊗ₘ 𝟙 (L.X j)) ≫
      HomologicalComplex.ιTensorObj K L p j (p + j) rfl))
  simp only [Category.assoc, tensorCyclesToCycles_iCycles]
  rw [tensorCyclesToTerm, Linear.units_smul_comp, Category.assoc, tensorInclusion_d,
    Preadditive.comp_add, Linear.comp_units_smul]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d,
    Category.id_comp, Category.comp_id, MonoidalPreadditive.zero_tensor,
    zero_comp, zero_add, smul_smul, Int.units_mul_self, one_smul]

/-- The short-complex boundary map is the original complex boundary
map into its original cycle object. -/
theorem sc_toCycles_eq (p : ℕ) :
    (K.sc p).toCycles = K.toCycles ((ComplexShape.up ℕ).prev p) p := by
  apply (cancel_mono (K.iCycles p)).mp
  rw [HomologicalComplex.toCycles_i]
  exact (K.sc p).toCycles_i

/-- The original tensor-of-cycles pairing kills every first boundary. -/
theorem tensorCyclesPairing_left_zero (p q n : ℕ) (h : p + q = n) :
    (K.sc p).toCycles ≫ ModuleCat.ofHom (tensorCyclesPairing K L p q n h) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change tensorCyclesPairing K L p q n h ((K.sc p).toCycles x) y = 0
  rw [sc_toCycles_eq]
  by_cases hi : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev p) p
  · have hh := tensorCyclesToCycles_left_boundary K L ((ComplexShape.up ℕ).prev p)
      p q n hi h
    have he := congrArg ModuleCat.Hom.hom hh
    simp only [ModuleCat.hom_comp, ModuleCat.hom_tensorHom,
      ModuleCat.hom_id, ModuleCat.hom_zero] at he
    have hv := LinearMap.congr_fun he (x ⊗ₜ[R] y)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hv
    exact hv
  · rw [HomologicalComplex.toCycles_eq_zero K hi]
    simp

/-- The original tensor-of-cycles pairing kills every second boundary. -/
theorem tensorCyclesPairing_right_zero (p q n : ℕ) (h : p + q = n)
    (x : K.cycles p) :
    (L.sc q).toCycles ≫ ModuleCat.ofHom (tensorCyclesPairing K L p q n h x) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change tensorCyclesPairing K L p q n h x ((L.sc q).toCycles y) = 0
  rw [sc_toCycles_eq]
  by_cases hj : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev q) q
  · have hh := tensorCyclesToCycles_right_boundary K L p ((ComplexShape.up ℕ).prev q)
      q n hj h
    have he := congrArg ModuleCat.Hom.hom hh
    simp only [ModuleCat.hom_comp, ModuleCat.hom_tensorHom,
      ModuleCat.hom_id, ModuleCat.hom_zero] at he
    have hv := LinearMap.congr_fun he (x ⊗ₜ[R] y)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hv
    exact hv
  · rw [HomologicalComplex.toCycles_eq_zero L hj]
    simp

/-- The canonical bilinear pairing on the original homology objects,
constructed by descent of the original tensor-of-cycles map. -/
def tensorHomologyPairing (p q n : ℕ) (h : p + q = n) :
    K.homology p →ₗ[R] L.homology q →ₗ[R] (HomologicalComplex.tensorObj K L).homology n :=
  ShortComplex.homologyBilinearDesc (K.sc p) (L.sc q)
    ((HomologicalComplex.tensorObj K L).homology n)
    (tensorCyclesPairing K L p q n h) (tensorCyclesPairing_left_zero K L p q n h)
    (tensorCyclesPairing_right_zero K L p q n h)

/-- The original tensor-of-cycles map descends to the canonical map from
the tensor product of the original homology groups. -/
def tensorHomologyMap (p q n : ℕ) (h : p + q = n) :
    K.homology p ⊗[R] L.homology q →ₗ[R] (HomologicalComplex.tensorObj K L).homology n :=
  TensorProduct.lift (tensorHomologyPairing K L p q n h)

/-- The canonical map sends the tensor of original cycle classes to
the class of their original tensor. No splitting occurs in this formula. -/
theorem tensorHomologyMap_homologyπ_tmul (p q n : ℕ) (h : p + q = n)
    (x : K.cycles p) (y : L.cycles q) :
    tensorHomologyMap K L p q n h (K.homologyπ p x ⊗ₜ[R] L.homologyπ q y) =
      (HomologicalComplex.tensorObj K L).homologyπ n
        (tensorCyclesToCycles K L p q n h (x ⊗ₜ[R] y)) := by
  rw [tensorHomologyMap, TensorProduct.lift.tmul]
  exact ShortComplex.homologyBilinearDesc_apply_homologyπ (K.sc p) (L.sc q)
    ((HomologicalComplex.tensorObj K L).homology n) _ _ _ x y

/-- The original finite antidiagonal sum of tensor products of the
original homology groups. -/
abbrev homologyTensorSum (n : ℕ) : Type u :=
  DirectSum (HomologicalComplex₂.TotalDegree n)
    (fun s => K.homology s.val.1 ⊗[R] L.homology s.val.2)

/-- The canonical Künneth map, obtained by summing the original
tensor-of-cycles descent over the native finite antidiagonal. -/
def map (n : ℕ) : homologyTensorSum K L n →ₗ[R]
    (HomologicalComplex.tensorObj K L).homology n :=
  DirectSum.toModule R _ _
    (fun s : HomologicalComplex₂.TotalDegree n =>
      tensorHomologyMap K L s.val.1 s.val.2 n s.property)

/-- Every original homogeneous tensor summand is mapped by its original
tensor-of-cycles descent. -/
@[simp]
theorem map_lof (n : ℕ) (s : HomologicalComplex₂.TotalDegree n)
    (z : K.homology s.val.1 ⊗[R] L.homology s.val.2) :
    map K L n (DirectSum.lof R _ _ s z) =
      tensorHomologyMap K L s.val.1 s.val.2 n s.property z := by
  unfold map
  exact DirectSum.toModule_lof
    (φ := fun t : HomologicalComplex₂.TotalDegree n =>
      tensorHomologyMap K L t.val.1 t.val.2 n t.property) R s z

/-- The canonical Künneth map has the literal original cycle-tensor
formula before any internal splitting is used to prove bijectivity. -/
theorem map_lof_homologyπ_tmul (p q n : ℕ) (h : p + q = n)
    (x : K.cycles p) (y : L.cycles q) :
    map K L n (DirectSum.lof R _ _ (⟨(p, q), h⟩ : HomologicalComplex₂.TotalDegree n)
      (K.homologyπ p x ⊗ₜ[R] L.homologyπ q y)) =
      (HomologicalComplex.tensorObj K L).homologyπ n
        (tensorCyclesToCycles K L p q n h (x ⊗ₜ[R] y)) := by
  rw [map_lof, tensorHomologyMap_homologyπ_tmul]

variable {K L} {K' L' : CochainComplex (ModuleCat.{u} R) ℕ}

/-- The native tensor inclusion is natural for the original tensor map
of complexes. -/
theorem tensorInclusion_naturality (f : K ⟶ K') (g : L ⟶ L')
    (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj K' L' p q n h := by
  have e := HomologicalComplex.ι_mapBifunctorMap f g
    (curriedTensor (ModuleCat.{u} R)) (.up ℕ) p q n h
  simpa only [curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def, Category.assoc] using e

/-- Naturality of the original cycle tensor map at the term level. -/
theorem tensorCyclesToTerm_naturality (f : K ⟶ K') (g : L ⟶ L')
    (p q n : ℕ) (h : p + q = n) :
    (HomologicalComplex.cyclesMap f p ⊗ₘ HomologicalComplex.cyclesMap g q) ≫
        tensorCyclesToTerm K' L' p q n h =
      tensorCyclesToTerm K L p q n h ≫ (HomologicalComplex.tensorHom f g).f n := by
  rw [tensorCyclesToTerm, tensorCyclesToTerm, Category.assoc, tensorInclusion_naturality]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    HomologicalComplex.cyclesMap_i]

/-- The whole original lift into tensor-total cycles is natural. -/
theorem tensorCyclesToCycles_naturality (f : K ⟶ K') (g : L ⟶ L')
    (p q n : ℕ) (h : p + q = n) :
    (HomologicalComplex.cyclesMap f p ⊗ₘ HomologicalComplex.cyclesMap g q) ≫
        tensorCyclesToCycles K' L' p q n h =
      tensorCyclesToCycles K L p q n h ≫
        HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom f g) n := by
  apply (cancel_mono ((HomologicalComplex.tensorObj K' L').iCycles n)).mp
  simp only [Category.assoc, tensorCyclesToCycles_iCycles,
    HomologicalComplex.cyclesMap_i, tensorCyclesToCycles_iCycles_assoc]
  exact tensorCyclesToTerm_naturality f g p q n h

/-- Naturality of the original tensor cycle-class map, before descent. -/
theorem tensorCyclesToHomology_naturality (f : K ⟶ K') (g : L ⟶ L')
    (p q n : ℕ) (h : p + q = n) :
    (tensorCyclesToCycles K L p q n h ≫ (HomologicalComplex.tensorObj K L).homologyπ n) ≫
        HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) n =
      (HomologicalComplex.cyclesMap f p ⊗ₘ HomologicalComplex.cyclesMap g q) ≫
        tensorCyclesToCycles K' L' p q n h ≫ (HomologicalComplex.tensorObj K' L').homologyπ n := by
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, ← tensorCyclesToCycles_naturality, Category.assoc]

/-- The whole canonical tensor map on original homology is natural. -/
theorem tensorHomologyMap_naturality (f : K ⟶ K') (g : L ⟶ L')
    (p q n : ℕ) (h : p + q = n) :
    (HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) n).hom ∘ₗ
        tensorHomologyMap K L p q n h =
      tensorHomologyMap K' L' p q n h ∘ₗ
        TensorProduct.map (HomologicalComplex.homologyMap f p).hom
          (HomologicalComplex.homologyMap g q).hom := by
  apply TensorProduct.ext'
  intro x y
  obtain ⟨x, rfl⟩ := ShortComplex.homologyπ_surjective (K.sc p) x
  obtain ⟨y, rfl⟩ := ShortComplex.homologyπ_surjective (L.sc q) y
  have hf : (HomologicalComplex.homologyMap f p).hom (K.homologyπ p x) =
      K'.homologyπ p (HomologicalComplex.cyclesMap f p x) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f p) x
  have hg : (HomologicalComplex.homologyMap g q).hom (L.homologyπ q y) =
      L'.homologyπ q (HomologicalComplex.cyclesMap g q y) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality g q) y
  change (HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) n).hom
      (tensorHomologyMap K L p q n h (K.homologyπ p x ⊗ₜ[R] L.homologyπ q y)) =
    tensorHomologyMap K' L' p q n h
      ((HomologicalComplex.homologyMap f p).hom (K.homologyπ p x) ⊗ₜ[R]
        (HomologicalComplex.homologyMap g q).hom (L.homologyπ q y))
  rw [tensorHomologyMap_homologyπ_tmul, hf, hg, tensorHomologyMap_homologyπ_tmul]
  have he := congrArg ModuleCat.Hom.hom (tensorCyclesToHomology_naturality f g p q n h)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_tensorHom] at he
  have hv := LinearMap.congr_fun he (x ⊗ₜ[R] y)
  simp only [LinearMap.comp_apply] at hv
  exact hv

/-- The original componentwise homology tensor maps on the original
finite antidiagonal direct sum. -/
def homologyTensorSumMap (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    homologyTensorSum K L n →ₗ[R] homologyTensorSum K' L' n :=
  DirectSum.lmap (fun s : HomologicalComplex₂.TotalDegree n =>
    TensorProduct.map (HomologicalComplex.homologyMap f s.val.1).hom
      (HomologicalComplex.homologyMap g s.val.2).hom)

/-- Naturality of the complete canonical antidiagonal Künneth map. -/
theorem map_naturality (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    (HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) n).hom ∘ₗ map K L n =
      map K' L' n ∘ₗ homologyTensorSumMap f g n := by
  apply DirectSum.linearMap_ext R
  intro s
  apply LinearMap.ext
  intro z
  change (HomologicalComplex.homologyMap (HomologicalComplex.tensorHom f g) n).hom
      (map K L n (DirectSum.lof R _ _ s z)) =
    map K' L' n (homologyTensorSumMap f g n (DirectSum.lof R _ _ s z))
  rw [map_lof, homologyTensorSumMap, DirectSum.lmap_lof, map_lof]
  exact LinearMap.congr_fun (tensorHomologyMap_naturality f g s.val.1 s.val.2 n s.property) z

variable (K L)

/-- The ordinary module braiding identifies the flipped original
bicomplex with the original tensor bicomplex in reversed order. -/
def tensorFlipBicomplexIso : (tensorBicomplex K L).flip ≅ tensorBicomplex L K where
  hom := HomologicalComplex₂.homMk
    (fun s => (β_ (K.X s.2) (L.X s.1)).hom)
    (by
      intro p p' q _
      change (β_ (K.X q) (L.X p)).hom ≫ L.d p p' ▷ K.X q =
        K.X q ◁ L.d p p' ≫ (β_ (K.X q) (L.X p')).hom
      exact (braiding_naturality_right (K.X q) (L.d p p')).symm)
    (by
      intro p q q' _
      change (β_ (K.X q) (L.X p)).hom ≫ L.X p ◁ K.d q q' =
        K.d q q' ▷ L.X p ≫ (β_ (K.X q') (L.X p)).hom
      exact (braiding_naturality_left (K.d q q') (L.X p)).symm)
  inv := HomologicalComplex₂.homMk
    (fun s => (β_ (K.X s.2) (L.X s.1)).inv)
    (by
      intro p p' q _
      change (β_ (K.X q) (L.X p)).inv ≫ K.X q ◁ L.d p p' =
        L.d p p' ▷ K.X q ≫ (β_ (K.X q) (L.X p')).inv
      exact (braiding_inv_naturality_left (L.d p p') (K.X q)).symm)
    (by
      intro p q q' _
      change (β_ (K.X q) (L.X p)).inv ≫ K.d q q' ▷ L.X p =
        L.X p ◁ K.d q q' ≫ (β_ (K.X q') (L.X p)).inv
      exact (braiding_inv_naturality_right (L.X p) (K.d q q')).symm)
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    exact (β_ (K.X q) (L.X p)).hom_inv_id
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    exact (β_ (K.X q) (L.X p)).inv_hom_id

/-- The signed tensor swap on the original native tensor total. The
sign comes from the native total flip, before the ordinary module braiding. -/
def tensorSwap : HomologicalComplex.tensorObj K L ≅ HomologicalComplex.tensorObj L K :=
  (HomologicalComplex.mapBifunctorFlipIso K L (curriedTensor (ModuleCat.{u} R))
    (.up ℕ)).symm ≪≫
      HomologicalComplex₂.total.mapIso (tensorFlipBicomplexIso K L) (.up ℕ)

/-- The signed swap sends an original `(p,q)` tensor summand to the
original `(q,p)` summand with its Koszul sign. -/
theorem tensorInclusion_swap (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (tensorSwap K L).hom.f n =
      (-1 : ℤˣ) ^ (p * q) • ((β_ (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιTensorObj L K q p n (by omega)) := by
  change HomologicalComplex.ιTensorObj K L p q n h ≫
      ((HomologicalComplex.mapBifunctorFlipIso K L
        (curriedTensor (ModuleCat.{u} R)) (.up ℕ)).inv ≫
          HomologicalComplex₂.total.map (tensorFlipBicomplexIso K L).hom (.up ℕ)).f n = _
  rw [HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex.ι_mapBifunctorFlipIso_inv, Linear.units_smul_comp,
    HomologicalComplex₂.ιTotal_map]
  rfl

/-- The signed swap is compatible with the original lifted tensor of
cycles, including its full Koszul factor. -/
theorem tensorCyclesToCycles_swap (p q n : ℕ) (h : p + q = n) :
    tensorCyclesToCycles K L p q n h ≫
        HomologicalComplex.cyclesMap (tensorSwap K L).hom n =
      (-1 : ℤˣ) ^ (p * q) • ((β_ (K.cycles p) (L.cycles q)).hom ≫
        tensorCyclesToCycles L K q p n (by omega)) := by
  apply (cancel_mono ((HomologicalComplex.tensorObj L K).iCycles n)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i,
    tensorCyclesToCycles_iCycles_assoc, Linear.units_smul_comp,
    Category.assoc, tensorCyclesToCycles_iCycles]
  rw [tensorCyclesToTerm, tensorCyclesToTerm, Category.assoc,
    tensorInclusion_swap, Linear.comp_units_smul]
  congr 1
  rw [← Category.assoc, braiding_naturality, Category.assoc]

/-- Koszul symmetry for the whole canonical homogeneous homology map. -/
theorem tensorHomologyMap_swap (p q n : ℕ) (h : p + q = n) :
    (HomologicalComplex.homologyMap (tensorSwap K L).hom n).hom ∘ₗ
        tensorHomologyMap K L p q n h =
      (-1 : ℤˣ) ^ (p * q) •
        (tensorHomologyMap L K q p n (by omega) ∘ₗ
          (TensorProduct.comm R (K.homology p) (L.homology q)).toLinearMap) := by
  apply TensorProduct.ext'
  intro a b
  obtain ⟨x, rfl⟩ := ShortComplex.homologyπ_surjective (K.sc p) a
  obtain ⟨y, rfl⟩ := ShortComplex.homologyπ_surjective (L.sc q) b
  change (HomologicalComplex.homologyMap (tensorSwap K L).hom n).hom
      (tensorHomologyMap K L p q n h (K.homologyπ p x ⊗ₜ[R] L.homologyπ q y)) =
    (-1 : ℤˣ) ^ (p * q) • tensorHomologyMap L K q p n (by omega)
      (L.homologyπ q y ⊗ₜ[R] K.homologyπ p x)
  rw [tensorHomologyMap_homologyπ_tmul, tensorHomologyMap_homologyπ_tmul]
  have e : (tensorCyclesToCycles K L p q n h ≫
      (HomologicalComplex.tensorObj K L).homologyπ n) ≫
        HomologicalComplex.homologyMap (tensorSwap K L).hom n =
      (-1 : ℤˣ) ^ (p * q) • ((β_ (K.cycles p) (L.cycles q)).hom ≫
        tensorCyclesToCycles L K q p n (by omega) ≫
          (HomologicalComplex.tensorObj L K).homologyπ n) := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
      ← Category.assoc, tensorCyclesToCycles_swap, Linear.units_smul_comp, Category.assoc]
  have he := congrArg ModuleCat.Hom.hom e
  simp only [ModuleCat.hom_comp, ModuleCat.hom_smul] at he
  have hv := LinearMap.congr_fun he (x ⊗ₜ[R] y)
  exact hv

/-- The original tensor-complex associator preserves each original
triple tensor inclusion without an additional sign. -/
theorem tensorInclusion_associativity (M : CochainComplex (ModuleCat.{u} R) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    (HomologicalComplex.ιTensorObj K L p q (p + q) rfl ⊗ₘ 𝟙 (M.X r)) ≫
        HomologicalComplex.ιTensorObj (HomologicalComplex.tensorObj K L) M
          (p + q) r n h ≫ (HomologicalComplex.associator K L M).hom.f n =
      (α_ (K.X p) (L.X q) (M.X r)).hom ≫
        (𝟙 (K.X p) ⊗ₘ HomologicalComplex.ιTensorObj L M q r (q + r) rfl) ≫
          HomologicalComplex.ιTensorObj K (HomologicalComplex.tensorObj L M)
            p (q + r) n (by omega) := by
  have e := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso (ModuleCat.{u} R)) K L M (.up ℕ) (.up ℕ) (.up ℕ)
      p q r n h
  rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
  exact e

/-- Associativity on the original tensor cycle lifts, through the native
associator of tensor complexes. -/
theorem tensorCyclesToCycles_associativity (M : CochainComplex (ModuleCat.{u} R) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    (tensorCyclesToCycles K L p q (p + q) rfl ⊗ₘ 𝟙 (M.cycles r)) ≫
        tensorCyclesToCycles (HomologicalComplex.tensorObj K L) M (p + q) r n h ≫
          HomologicalComplex.cyclesMap (HomologicalComplex.associator K L M).hom n =
      (α_ (K.cycles p) (L.cycles q) (M.cycles r)).hom ≫
        (𝟙 (K.cycles p) ⊗ₘ tensorCyclesToCycles L M q r (q + r) rfl) ≫
          tensorCyclesToCycles K (HomologicalComplex.tensorObj L M) p (q + r) n
            (by omega) := by
  have hleft :
      (tensorCyclesToCycles K L p q (p + q) rfl ⊗ₘ 𝟙 (M.cycles r)) ≫
          tensorCyclesToTerm (HomologicalComplex.tensorObj K L) M (p + q) r n h =
        ((K.iCycles p ⊗ₘ L.iCycles q) ⊗ₘ M.iCycles r) ≫
          (HomologicalComplex.ιTensorObj K L p q (p + q) rfl ⊗ₘ 𝟙 (M.X r)) ≫
            HomologicalComplex.ιTensorObj (HomologicalComplex.tensorObj K L) M
              (p + q) r n h := by
    simp only [tensorCyclesToTerm, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
      tensorCyclesToCycles_iCycles]
  have hright :
      (𝟙 (K.cycles p) ⊗ₘ tensorCyclesToCycles L M q r (q + r) rfl) ≫
          tensorCyclesToTerm K (HomologicalComplex.tensorObj L M) p (q + r) n (by omega) =
        (K.iCycles p ⊗ₘ (L.iCycles q ⊗ₘ M.iCycles r)) ≫
          (𝟙 (K.X p) ⊗ₘ HomologicalComplex.ιTensorObj L M q r (q + r) rfl) ≫
            HomologicalComplex.ιTensorObj K (HomologicalComplex.tensorObj L M)
              p (q + r) n (by omega) := by
    simp only [tensorCyclesToTerm, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
      tensorCyclesToCycles_iCycles]
  apply (cancel_mono ((HomologicalComplex.tensorObj K
    (HomologicalComplex.tensorObj L M)).iCycles n)).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    tensorCyclesToCycles_iCycles_assoc, tensorCyclesToCycles_iCycles]
  rw [← Category.assoc, hleft]
  simp only [Category.assoc]
  rw [tensorInclusion_associativity, MonoidalCategory.associator_naturality_assoc, ← hright]

/-- The original degree-zero cycle representing the tensor unit. -/
def tensorUnitCycle : 𝟙_ (ModuleCat.{u} R) ⟶
    (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)).cycles 0 :=
  (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)).liftCycles
    (HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv 1
      (by simp) (by rw [HomologicalComplex.single_obj_d, comp_zero])

@[reassoc (attr := simp)]
theorem tensorUnitCycle_iCycles :
    tensorUnitCycle (R := R) ≫
        (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)).iCycles 0 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The original scalar-to-homology map for the tensor unit. -/
def tensorUnitHomology : R →ₗ[R]
    (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)).homology 0 :=
  (tensorUnitCycle (R := R) ≫
    (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)).homologyπ 0).hom

/-- Normalization of the original left unitor on its degree-zero
homogeneous tensor inclusion. -/
theorem tensorInclusion_leftUnitor (n : ℕ) :
    ((HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv ⊗ₘ
        𝟙 (K.X n)) ≫
      HomologicalComplex.ιTensorObj (HomologicalComplex.tensorUnit (ModuleCat.{u} R)
        (.up ℕ)) K 0 n n (zero_add n) ≫ (HomologicalComplex.leftUnitor K).hom.f n =
        (λ_ (K.X n)).hom := by
  let e := (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) n).mapIso
    (HomologicalComplex.leftUnitor K)
  change _ ≫ _ ≫ e.hom = _
  apply (cancel_mono e.inv).mp
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he : e.inv = (λ_ (K.X n)).inv ≫
      ((HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv ▷
        K.X n) ≫ HomologicalComplex.ιTensorObj
          (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)) K 0 n n (zero_add n) :=
    HomologicalComplex.leftUnitor'_inv K n
  rw [he, Iso.hom_inv_id_assoc, MonoidalCategory.tensorHom_id]

/-- Normalization of the original right unitor on its degree-zero
homogeneous tensor inclusion. -/
theorem tensorInclusion_rightUnitor (n : ℕ) :
    (𝟙 (K.X n) ⊗ₘ
        (HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv) ≫
      HomologicalComplex.ιTensorObj K (HomologicalComplex.tensorUnit (ModuleCat.{u} R)
        (.up ℕ)) n 0 n (add_zero n) ≫ (HomologicalComplex.rightUnitor K).hom.f n =
        (ρ_ (K.X n)).hom := by
  let e := (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) n).mapIso
    (HomologicalComplex.rightUnitor K)
  change _ ≫ _ ≫ e.hom = _
  apply (cancel_mono e.inv).mp
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he : e.inv = (ρ_ (K.X n)).inv ≫
      (K.X n ◁ (HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv) ≫
        HomologicalComplex.ιTensorObj K
          (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)) n 0 n (add_zero n) :=
    HomologicalComplex.rightUnitor'_inv K n
  rw [he, Iso.hom_inv_id_assoc, MonoidalCategory.id_tensorHom]

/-- The original left unitor acts on the canonical tensor of cycles by
the ordinary scalar action on the original cycle module. -/
theorem tensorCyclesToCycles_leftUnitor (n : ℕ) :
    (tensorUnitCycle (R := R) ⊗ₘ 𝟙 (K.cycles n)) ≫
        tensorCyclesToCycles (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ))
          K 0 n n (zero_add n) ≫
            HomologicalComplex.cyclesMap (HomologicalComplex.leftUnitor K).hom n =
      (λ_ (K.cycles n)).hom := by
  apply (cancel_mono (K.iCycles n)).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    tensorCyclesToCycles_iCycles_assoc, tensorCyclesToTerm]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, tensorUnitCycle_iCycles,
    Category.id_comp]
  have e :
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv ⊗ₘ
          K.iCycles n =
        (𝟙 (𝟙_ (ModuleCat.{u} R)) ⊗ₘ K.iCycles n) ≫
          ((HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv ⊗ₘ
            𝟙 (K.X n)) := by
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [e, Category.assoc, tensorInclusion_leftUnitor,
    MonoidalCategory.id_tensorHom, MonoidalCategory.leftUnitor_naturality]

/-- The original right unitor acts on the canonical tensor of cycles by
the ordinary scalar action on the original cycle module. -/
theorem tensorCyclesToCycles_rightUnitor (n : ℕ) :
    (𝟙 (K.cycles n) ⊗ₘ tensorUnitCycle (R := R)) ≫
        tensorCyclesToCycles K
          (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)) n 0 n (add_zero n) ≫
            HomologicalComplex.cyclesMap (HomologicalComplex.rightUnitor K).hom n =
      (ρ_ (K.cycles n)).hom := by
  apply (cancel_mono (K.iCycles n)).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    tensorCyclesToCycles_iCycles_assoc, tensorCyclesToTerm]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, tensorUnitCycle_iCycles,
    Category.id_comp]
  have e : K.iCycles n ⊗ₘ
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv =
        (K.iCycles n ⊗ₘ 𝟙 (𝟙_ (ModuleCat.{u} R))) ≫
          (𝟙 (K.X n) ⊗ₘ
            (HomologicalComplex.singleObjXSelf (.up ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv) := by
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [e, Category.assoc, tensorInclusion_rightUnitor,
    MonoidalCategory.tensorHom_id, MonoidalCategory.rightUnitor_naturality]

/-- Associativity of the canonical homology tensor pairing through the
original tensor-complex associator. -/
theorem tensorHomologyMap_associativity (M : CochainComplex (ModuleCat.{u} R) ℕ)
    (p q r n : ℕ) (h : p + q + r = n)
    (a : K.homology p) (b : L.homology q) (c : M.homology r) :
    HomologicalComplex.homologyMap (HomologicalComplex.associator K L M).hom n
      (tensorHomologyMap (HomologicalComplex.tensorObj K L) M (p + q) r n h
        (tensorHomologyMap K L p q (p + q) rfl (a ⊗ₜ[R] b) ⊗ₜ[R] c)) =
      tensorHomologyMap K (HomologicalComplex.tensorObj L M) p (q + r) n (by omega)
        (a ⊗ₜ[R] tensorHomologyMap L M q r (q + r) rfl (b ⊗ₜ[R] c)) := by
  obtain ⟨x, rfl⟩ := ShortComplex.homologyπ_surjective (K.sc p) a
  obtain ⟨y, rfl⟩ := ShortComplex.homologyπ_surjective (L.sc q) b
  obtain ⟨z, rfl⟩ := ShortComplex.homologyπ_surjective (M.sc r) c
  change HomologicalComplex.homologyMap (HomologicalComplex.associator K L M).hom n
      (tensorHomologyMap (HomologicalComplex.tensorObj K L) M (p + q) r n h
        (tensorHomologyMap K L p q (p + q) rfl
          (K.homologyπ p x ⊗ₜ[R] L.homologyπ q y) ⊗ₜ[R] M.homologyπ r z)) =
    tensorHomologyMap K (HomologicalComplex.tensorObj L M) p (q + r) n (by omega)
      (K.homologyπ p x ⊗ₜ[R] tensorHomologyMap L M q r (q + r) rfl
        (L.homologyπ q y ⊗ₜ[R] M.homologyπ r z))
  simp only [tensorHomologyMap_homologyπ_tmul]
  have e := congrArg (fun t => t ≫
      (HomologicalComplex.tensorObj K (HomologicalComplex.tensorObj L M)).homologyπ n)
    (tensorCyclesToCycles_associativity K L M p q r n h)
  simp only [Category.assoc] at e
  rw [← HomologicalComplex.homologyπ_naturality] at e
  exact ConcreteCategory.congr_hom e ((x ⊗ₜ[R] y) ⊗ₜ[R] z)

/-- The canonical homology tensor pairing preserves the original left
unit, with the original scalar action on every homology group. -/
theorem tensorHomologyMap_leftUnitor (n : ℕ) (r : R) (a : K.homology n) :
    HomologicalComplex.homologyMap (HomologicalComplex.leftUnitor K).hom n
      (tensorHomologyMap (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ))
        K 0 n n (zero_add n) (tensorUnitHomology r ⊗ₜ[R] a)) = r • a := by
  obtain ⟨x, rfl⟩ := ShortComplex.homologyπ_surjective (K.sc n) a
  change HomologicalComplex.homologyMap (HomologicalComplex.leftUnitor K).hom n
      (tensorHomologyMap (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ))
        K 0 n n (zero_add n)
        ((HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)).homologyπ 0
          (tensorUnitCycle r) ⊗ₜ[R] K.homologyπ n x)) = r • K.homologyπ n x
  rw [tensorHomologyMap_homologyπ_tmul]
  have e := congrArg (fun t => t ≫ K.homologyπ n)
    (tensorCyclesToCycles_leftUnitor K n)
  simp only [Category.assoc] at e
  rw [← HomologicalComplex.homologyπ_naturality] at e
  have hv := ConcreteCategory.congr_hom e (r ⊗ₜ[R] x)
  change HomologicalComplex.homologyMap (HomologicalComplex.leftUnitor K).hom n
      ((HomologicalComplex.tensorObj
        (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)) K).homologyπ n
          (tensorCyclesToCycles
            (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)) K 0 n n (zero_add n)
              (tensorUnitCycle r ⊗ₜ[R] x))) = K.homologyπ n (r • x) at hv
  rw [map_smul] at hv
  exact hv

/-- The canonical homology tensor pairing preserves the original right
unit, with the original scalar action on every homology group. -/
theorem tensorHomologyMap_rightUnitor (n : ℕ) (a : K.homology n) (r : R) :
    HomologicalComplex.homologyMap (HomologicalComplex.rightUnitor K).hom n
      (tensorHomologyMap K (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ))
        n 0 n (add_zero n) (a ⊗ₜ[R] tensorUnitHomology r)) = r • a := by
  obtain ⟨x, rfl⟩ := ShortComplex.homologyπ_surjective (K.sc n) a
  change HomologicalComplex.homologyMap (HomologicalComplex.rightUnitor K).hom n
      (tensorHomologyMap K (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ))
        n 0 n (add_zero n)
        (K.homologyπ n x ⊗ₜ[R]
          (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)).homologyπ 0
            (tensorUnitCycle r))) = r • K.homologyπ n x
  rw [tensorHomologyMap_homologyπ_tmul]
  have e := congrArg (fun t => t ≫ K.homologyπ n)
    (tensorCyclesToCycles_rightUnitor K n)
  simp only [Category.assoc] at e
  rw [← HomologicalComplex.homologyπ_naturality] at e
  have hv := ConcreteCategory.congr_hom e (x ⊗ₜ[R] r)
  change HomologicalComplex.homologyMap (HomologicalComplex.rightUnitor K).hom n
      ((HomologicalComplex.tensorObj K
        (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ))).homologyπ n
          (tensorCyclesToCycles K
            (HomologicalComplex.tensorUnit (ModuleCat.{u} R) (.up ℕ)) n 0 n (add_zero n)
              (x ⊗ₜ[R] tensorUnitCycle r))) = K.homologyπ n (r • x) at hv
  rw [map_smul] at hv
  exact hv

/-- Tensoring quasi-isomorphisms of first-quadrant complexes preserves
quasi-isomorphisms when the terms needed in each variable are flat. The
proof uses the original bicomplex, its signed flip, and its native total. -/
theorem quasiIso_tensorHom_of_flat {K L K' L' : CochainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g]
    [∀ p, Module.Flat R (K'.X p)] [∀ q, Module.Flat R (L.X q)] :
    QuasiIso (HomologicalComplex.tensorHom f g) := by
  let φ : tensorBicomplex K L ⟶ tensorBicomplex K' L :=
    (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
      (.up ℕ) (.up ℕ)).map f).app L
  let ψ : tensorBicomplex K' L ⟶ tensorBicomplex K' L' :=
    (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
      (.up ℕ) (.up ℕ)).obj K').map g
  have hφflip : QuasiIso (HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor (ModuleCat.{u} R) (.up ℕ) (.up ℕ)).map φ)
        (.up ℕ)) := by
    apply HomologicalComplex₂.quasiIso_total_of_rowwise
    intro q
    change QuasiIso (((tensorRight (L.X q)).mapHomologicalComplex (.up ℕ)).map f)
    have : PreservesFiniteColimits (tensorRight (L.X q)) :=
      preservesFiniteColimits_of_natIso (tensorLeftIsoTensorRight (L.X q))
    infer_instance
  have : QuasiIso (HomologicalComplex₂.total.map φ (.up ℕ)) := by
    have := hφflip
    have : QuasiIso (((tensorBicomplex K L).totalFlipIso (.up ℕ)).hom ≫
        HomologicalComplex₂.total.map φ (.up ℕ)) := by
      rw [← HomologicalComplex₂.totalFlipIso_naturality φ]
      infer_instance
    exact quasiIso_of_comp_left
      ((tensorBicomplex K L).totalFlipIso (.up ℕ)).hom _
  have : QuasiIso (HomologicalComplex₂.total.map ψ (.up ℕ)) := by
    apply HomologicalComplex₂.quasiIso_total_of_rowwise
    intro p
    change QuasiIso (((tensorLeft (K'.X p)).mapHomologicalComplex (.up ℕ)).map g)
    infer_instance
  change QuasiIso (HomologicalComplex₂.total.map (φ ≫ ψ) (.up ℕ))
  rw [HomologicalComplex₂.total.map_comp]
  infer_instance

section Field

variable {k : Type u} [Field k]

/-- The zero-differential homology complex is used only inside the
bijectivity proof; the public Künneth map has already been defined by descent. -/
private def homologyZeroComplex (K : CochainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ where
  X n := K.homology n
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := zero_comp

private def cycleSection (K : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    K.homology n ⟶ K.cycles n :=
  ModuleCat.ofHom (Classical.choose ((K.homologyπ n).hom.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (ShortComplex.homologyπ_surjective (K.sc n)))))

private theorem cycleSection_comp (K : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    cycleSection K n ≫ K.homologyπ n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  exact Classical.choose_spec ((K.homologyπ n).hom.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (ShortComplex.homologyπ_surjective (K.sc n))))

private def homologyZeroToComplex (K : CochainComplex (ModuleCat.{u} k) ℕ) :
    homologyZeroComplex K ⟶ K where
  f n := cycleSection K n ≫ K.iCycles n
  comm' i j _ := by
    rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
    exact (zero_comp).symm

private theorem homologyZeroToComplex_cyclesMap (K : CochainComplex (ModuleCat.{u} k) ℕ)
    (n : ℕ) :
    HomologicalComplex.cyclesMap (homologyZeroToComplex K) n =
      (homologyZeroComplex K).iCycles n ≫ cycleSection K n := by
  apply (cancel_mono (K.iCycles n)).mp
  rw [HomologicalComplex.cyclesMap_i, Category.assoc]
  rfl

private theorem homologyZeroToComplex_quasiIso (K : CochainComplex (ModuleCat.{u} k) ℕ) :
    QuasiIso (homologyZeroToComplex K) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso ((homologyZeroComplex K).homologyπ n) :=
    ShortComplex.isIso_homologyπ ((homologyZeroComplex K).sc n) rfl
  have : IsIso ((homologyZeroComplex K).iCycles n) :=
    ShortComplex.isIso_iCycles ((homologyZeroComplex K).sc n) rfl
  have h : (homologyZeroComplex K).homologyπ n ≫
      HomologicalComplex.homologyMap (homologyZeroToComplex K) n =
        (homologyZeroComplex K).iCycles n := by
    rw [HomologicalComplex.homologyπ_naturality,
      homologyZeroToComplex_cyclesMap, Category.assoc, cycleSection_comp]
    exact Category.comp_id _
  have : IsIso ((homologyZeroComplex K).homologyπ n ≫
      HomologicalComplex.homologyMap (homologyZeroToComplex K) n) := h.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left ((homologyZeroComplex K).homologyπ n) _

variable (C D : CochainComplex (ModuleCat.{u} k) ℕ)

private abbrev homologyZeroTensor :=
  HomologicalComplex.tensorObj (homologyZeroComplex C) (homologyZeroComplex D)

private theorem homologyZeroTensor_d (n m : ℕ) : (homologyZeroTensor C D).d n m = 0 := by
  by_cases h : n + 1 = m
  · subst m
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [tensorInclusion_d]
    change (0 ⊗ₘ 𝟙 _) ≫ _ + (-1 : ℤˣ) ^ p • ((𝟙 _ ⊗ₘ 0) ≫ _) = _
    simp only [MonoidalPreadditive.zero_tensor, MonoidalPreadditive.tensor_zero,
      zero_comp, smul_zero, zero_add, comp_zero]
  · exact (homologyZeroTensor C D).shape n m h

private def homologyTensorSumIsoZeroTotal (n : ℕ) :
    ModuleCat.of k (homologyTensorSum C D n) ≅ (homologyZeroTensor C D).X n :=
  (ModuleCat.coprodIsoDirectSum (fun s : HomologicalComplex₂.TotalDegree n =>
    C.homology s.val.1 ⊗ D.homology s.val.2)).symm

private theorem homologyTensorSumIsoZeroTotal_lof (n : ℕ)
    (s : HomologicalComplex₂.TotalDegree n) :
    ModuleCat.ofHom (DirectSum.lof k _ _ s) ≫ (homologyTensorSumIsoZeroTotal C D n).hom =
      HomologicalComplex.ιTensorObj (homologyZeroComplex C) (homologyZeroComplex D)
        s.val.1 s.val.2 n s.property :=
  ModuleCat.lof_coprodIsoDirectSum_inv
    (fun t : HomologicalComplex₂.TotalDegree n => C.homology t.val.1 ⊗ D.homology t.val.2) s

private def zeroTensorCycleIso (n : ℕ) :
    (homologyZeroTensor C D).cycles n ≅ (homologyZeroTensor C D).X n :=
  ((homologyZeroTensor C D).sc n).cyclesIsoX₂ (homologyZeroTensor_d C D _ _)

private def zeroTensorTermHomologyIso (n : ℕ) :
    (homologyZeroTensor C D).X n ≅ (homologyZeroTensor C D).homology n :=
  (zeroTensorCycleIso C D n).symm ≪≫
    ((homologyZeroTensor C D).sc n).asIsoHomologyπ (homologyZeroTensor_d C D _ _)

private def zeroTensorToComplex : homologyZeroTensor C D ⟶ HomologicalComplex.tensorObj C D :=
  HomologicalComplex.tensorHom (homologyZeroToComplex C) (homologyZeroToComplex D)

private theorem zeroTensorToComplex_quasiIso : QuasiIso (zeroTensorToComplex C D) := by
  have := homologyZeroToComplex_quasiIso C
  have := homologyZeroToComplex_quasiIso D
  exact quasiIso_tensorHom_of_flat (homologyZeroToComplex C) (homologyZeroToComplex D)

private theorem zeroTensor_cycles_comparison (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj (homologyZeroComplex C) (homologyZeroComplex D) p q n h ≫
        (zeroTensorCycleIso C D n).inv ≫
          HomologicalComplex.cyclesMap (zeroTensorToComplex C D) n =
      (cycleSection C p ⊗ₘ cycleSection D q) ≫ tensorCyclesToCycles C D p q n h := by
  apply (cancel_mono ((HomologicalComplex.tensorObj C D).iCycles n)).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    tensorCyclesToCycles_iCycles]
  change HomologicalComplex.ιTensorObj (homologyZeroComplex C) (homologyZeroComplex D)
      p q n h ≫ (zeroTensorCycleIso C D n).inv ≫
        (zeroTensorCycleIso C D n).hom ≫ (zeroTensorToComplex C D).f n = _
  rw [Iso.inv_hom_id_assoc, zeroTensorToComplex, tensorInclusion_naturality]
  change ((cycleSection C p ≫ C.iCycles p) ⊗ₘ (cycleSection D q ≫ D.iCycles q)) ≫ _ = _
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  rfl

private theorem zeroTensor_homology_comparison (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj (homologyZeroComplex C) (homologyZeroComplex D) p q n h ≫
        (zeroTensorTermHomologyIso C D n).hom ≫
          HomologicalComplex.homologyMap (zeroTensorToComplex C D) n =
      (cycleSection C p ⊗ₘ cycleSection D q) ≫ tensorCyclesToCycles C D p q n h ≫
        (HomologicalComplex.tensorObj C D).homologyπ n := by
  change HomologicalComplex.ιTensorObj (homologyZeroComplex C) (homologyZeroComplex D)
      p q n h ≫ ((zeroTensorCycleIso C D n).inv ≫ (homologyZeroTensor C D).homologyπ n) ≫
        HomologicalComplex.homologyMap (zeroTensorToComplex C D) n = _
  simpa only [Category.assoc, HomologicalComplex.homologyπ_naturality] using
    congrArg (fun t => t ≫ (HomologicalComplex.tensorObj C D).homologyπ n)
      (zeroTensor_cycles_comparison C D p q n h)

private def comparisonIso (n : ℕ) : ModuleCat.of k (homologyTensorSum C D n) ≅
    (HomologicalComplex.tensorObj C D).homology n := by
  haveI := zeroTensorToComplex_quasiIso C D
  haveI : IsIso (HomologicalComplex.homologyMap (zeroTensorToComplex C D) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  exact homologyTensorSumIsoZeroTotal C D n ≪≫ zeroTensorTermHomologyIso C D n ≪≫
    asIso (HomologicalComplex.homologyMap (zeroTensorToComplex C D) n)

private theorem comparisonIso_lof (n : ℕ) (s : HomologicalComplex₂.TotalDegree n) :
    ModuleCat.ofHom (DirectSum.lof k _ _ s) ≫ (comparisonIso C D n).hom =
      (cycleSection C s.val.1 ⊗ₘ cycleSection D s.val.2) ≫
        tensorCyclesToCycles C D s.val.1 s.val.2 n s.property ≫
          (HomologicalComplex.tensorObj C D).homologyπ n := by
  change ModuleCat.ofHom (DirectSum.lof k _ _ s) ≫
      ((homologyTensorSumIsoZeroTotal C D n).hom ≫
        (zeroTensorTermHomologyIso C D n).hom ≫
          HomologicalComplex.homologyMap (zeroTensorToComplex C D) n) = _
  rw [← Category.assoc, homologyTensorSumIsoZeroTotal_lof,
    zeroTensor_homology_comparison]

private theorem comparisonIso_hom_eq_map (n : ℕ) :
    (comparisonIso C D n).hom.hom = map C D n := by
  apply DirectSum.linearMap_ext k
  intro s
  apply TensorProduct.ext'
  intro a b
  change (comparisonIso C D n).hom
      (DirectSum.lof k _ _ s (a ⊗ₜ[k] b)) =
    map C D n (DirectSum.lof k _ _ s (a ⊗ₜ[k] b))
  have hC : C.homologyπ s.val.1 (cycleSection C s.val.1 a) = a :=
    ConcreteCategory.congr_hom (cycleSection_comp C s.val.1) a
  have hD : D.homologyπ s.val.2 (cycleSection D s.val.2 b) = b :=
    ConcreteCategory.congr_hom (cycleSection_comp D s.val.2) b
  have ht := tensorHomologyMap_homologyπ_tmul C D s.val.1 s.val.2 n s.property
    (cycleSection C s.val.1 a) (cycleSection D s.val.2 b)
  rw [hC, hD] at ht
  rw [map_lof, ht]
  have hh := ConcreteCategory.congr_hom (comparisonIso_lof C D n s) (a ⊗ₜ[k] b)
  exact hh

/-- The canonical tensor-of-cycles map is bijective over every field.
Splittings occur only in this proof, and its conclusion is about the
original map on the original homology objects. -/
theorem map_bijective (n : ℕ) : Function.Bijective (map C D n) := by
  rw [← comparisonIso_hom_eq_map C D n]
  exact (comparisonIso C D n).toLinearEquiv.bijective

/-- The field Künneth equivalence has the original tensor-of-cycles map
as its forward map. No chosen splitting enters this public construction. -/
def equiv (n : ℕ) : homologyTensorSum C D n ≃ₗ[k]
    (HomologicalComplex.tensorObj C D).homology n :=
  LinearEquiv.ofBijective (map C D n) (map_bijective C D n)

@[simp]
theorem equiv_toLinearMap (n : ℕ) : (equiv C D n).toLinearMap = map C D n := rfl

end Field

end HomologicalComplex.Kunneth
