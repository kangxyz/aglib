/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Koszul
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.FreeDegree

/-!
# Exactness of the Koszul complex of the coordinates

For every module `F` on projective space with finitely many linearly ordered coordinates, over
every commutative base ring, the Koszul complex `K(t)` of the coordinates (`Regularity/Koszul`) is
exact in positive degrees (`epi_koszul_kernelLift`: `K_{p+2} ⟶ ker (K_{p+1} ⟶ K_p)` is an
epimorphism) and maps onto `K_0` (`epi_koszulDifferential_zero`).

The proof works in the monoidal structure of scheme modules. A coordinate `Xᵢ` is a morphism
`coordinateUnitHom i : 𝟙_ ⟶ O(1)`, multiplying every module by `unitMultiply` (`G ⟶ O(1) ⊗ G`),
and a module killed by every such multiplication is zero
(`isZero_of_unitMultiply_coordinate_eq_zero`, through the bridge
`twistingTensorMultiply_app_eq_unitMultiply`). The summandwise inverse composition isomorphisms
`koszulTwistInv : K_p(t + 1) ⟶ O(1) ⊗ K_p(t)` turn `unitMultiply` on `K_p(t)` into the
coordinate multiplication `K_p(t) ⟶ K_p(t + 1)` (`unitMultiply_koszulTerm`) and commute with the
differentials (`koszulDifferential_comp_twistInv`). With the Koszul null-homotopy
(`koszul_homotopy`, `koszul_homotopy_zero`), multiplication by `Xᵢ` on the cycles factors through
the boundaries, so the homology is killed by every coordinate (`epi_of_unitMultiply_factor`).

The composition isomorphisms enter as `twistMerge`/`twistMergeInv` of
`ProjectiveSpace/Tensor/Monoidal/FreeDegree`, whose declared types use the monoidal spelling
`O(a) ⊗ T_b.obj G`; every conversion between that spelling and the composite-functor spelling is
proved there once, at variable degrees.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-! ### Coordinate multiplication as multiplication by a unit morphism -/

open MonoidalCategory

/-- Whiskering by a module sheaf commutes with integer multiples. `MonoidalPreadditive` gives the
zero and sum forms, but no `zsmul` form. -/
theorem moduleWhiskerLeft_zsmul {X : Scheme.{u}} (M : X.Modules) {A B : X.Modules} (n : ℤ)
    (f : A ⟶ B) : M ◁ (n • f) = n • (M ◁ f) :=
  (moduleTensorLeftFunctor X M).map_zsmul

/-- The coordinate `Xᵢ` as a morphism `𝟙_ ⟶ O(1)` out of the monoidal unit. -/
abbrev coordinateUnitHom (i : ι) :
    𝟙_ (ProjectiveSpace R ι).Modules ⟶ twistingSheaf R ι ((1 : ℕ) : ℤ) :=
  twistingSectionUnitHom (coordinateSection R ι i)

-- The coordinate multiplication of `isZero_of_coordinate_eq_zero` is spelled with the twist
-- tensor functor; it is the monoidal composite only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- A module on which multiplication by every coordinate `Xᵢ : G ⟶ O(1) ⊗ G` vanishes is
zero. -/
theorem isZero_of_unitMultiply_coordinate_eq_zero (G : (ProjectiveSpace R ι).Modules)
    (h : ∀ i, unitMultiply (coordinateUnitHom R ι i) G = 0) : IsZero G := by
  apply isZero_of_coordinate_eq_zero R ι G
  intro i
  have h1 := whiskerLeft_unitMultiply (coordinateUnitHom R ι i) (twistingSheaf R ι (-1)) G
  rw [h i, MonoidalPreadditive.whiskerLeft_zero] at h1
  have hz : unitMultiply (coordinateUnitHom R ι i) (twistingSheaf R ι (-1) ⊗ G) = 0 := by
    rw [← cancel_mono ((α_ _ _ _).inv ≫ (β_ _ _).hom ▷ G ≫ (α_ _ _ _).hom), ← h1, zero_comp]
  rw [twistingTensorMultiply_app_eq_unitMultiply, hz, zero_comp]

variable [LinearOrder ι] [Fintype ι] (F : (ProjectiveSpace R ι).Modules)

/-! ### Comparing Koszul terms of different twists -/

/-- The summandwise inverse composition isomorphisms `K_p(t + 1) ⟶ O(1) ⊗ K_p(t)`. Only this
map out of the coproduct `K_p(t + 1)` is used, never its inverse. Its components carry the degree
proof `koszulDeg_shift` of `koszulCoordinateMul`, so that the two are compared syntactically. -/
def koszulTwistInv (t : ℤ) (p : ℕ) :
    koszulTerm R ι F (t + 1) p ⟶ twistingSheaf R ι ((1 : ℕ) : ℤ) ⊗ koszulTerm R ι F t p :=
  Sigma.desc fun J => twistMergeInv R ι ((1 : ℕ) : ℤ) (t - (p : ℤ)) (t + 1 - (p : ℤ))
      (koszulDeg_shift t p) F ≫
    twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ Sigma.ι (fun _ : KoszulIndex ι p =>
      (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (t - (p : ℤ)))).obj F) J

omit [LinearOrder ι] in
/-- On a summand, `koszulTwistInv` is the inverse composition isomorphism. -/
@[reassoc]
theorem ι_koszulTwistInv (t : ℤ) (p : ℕ) (J : KoszulIndex ι p) :
    Sigma.ι (fun _ : KoszulIndex ι p => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t + 1 - (p : ℤ)))).obj F) J ≫ koszulTwistInv R ι F t p =
      twistMergeInv R ι ((1 : ℕ) : ℤ) (t - (p : ℤ)) (t + 1 - (p : ℤ)) (koszulDeg_shift t p) F ≫
        twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ Sigma.ι (fun _ : KoszulIndex ι p =>
          (moduleTensorLeftFunctor (ProjectiveSpace R ι)
            (twistingSheaf R ι (t - (p : ℤ)))).obj F) J := by
  rw [koszulTwistInv, Sigma.ι_comp_desc]

omit [LinearOrder ι] [Fintype ι] in
/-- Multiplication by `Xᵢ` on `O(b) ⊗ F` is coordinate multiplication into `O(b') ⊗ F`
followed by the inverse composition isomorphism, for `1 + b = b'`. -/
theorem unitMultiply_coordinate_eq_koszulMul (i : ι) (b b' : ℤ) (h : ((1 : ℕ) : ℤ) + b = b') :
    unitMultiply (coordinateUnitHom R ι i)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj F) =
      koszulMul R ι F i b b' h ≫ twistMergeInv R ι ((1 : ℕ) : ℤ) b b' h F := by
  rw [← cancel_mono (twistMerge R ι ((1 : ℕ) : ℤ) b b' h F), Category.assoc,
    twistMergeInv_twistMerge, Category.comp_id]
  exact unitMultiply_twistMerge R ι ((1 : ℕ) : ℤ) b b' h (coordinateSection R ι i) F

omit [LinearOrder ι] in
/-- On a summand, multiplication by `Xᵢ` is coordinate multiplication followed by the inverse
composition isomorphism. -/
theorem ι_unitMultiply_koszulTerm (t : ℤ) (p : ℕ) (i : ι) (J : KoszulIndex ι p) :
    Sigma.ι (fun _ : KoszulIndex ι p => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - (p : ℤ)))).obj F) J ≫
        unitMultiply (coordinateUnitHom R ι i) (koszulTerm R ι F t p) =
      koszulMul R ι F i (t - (p : ℤ)) (t + 1 - (p : ℤ)) (koszulDeg_shift t p) ≫
        twistMergeInv R ι ((1 : ℕ) : ℤ) (t - (p : ℤ)) (t + 1 - (p : ℤ)) (koszulDeg_shift t p) F ≫
          twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ Sigma.ι (fun _ : KoszulIndex ι p =>
            (moduleTensorLeftFunctor (ProjectiveSpace R ι)
              (twistingSheaf R ι (t - (p : ℤ)))).obj F) J := by
  rw [unitMultiply_naturality, unitMultiply_coordinate_eq_koszulMul R ι F i (t - (p : ℤ))
    (t + 1 - (p : ℤ)) (koszulDeg_shift t p), Category.assoc]

omit [LinearOrder ι] in
/-- On a summand, coordinate multiplication followed by `koszulTwistInv` is coordinate
multiplication followed by the inverse composition isomorphism. -/
theorem ι_koszulCoordinateMul_twistInv (t : ℤ) (p : ℕ) (i : ι) (J : KoszulIndex ι p) :
    Sigma.ι (fun _ : KoszulIndex ι p => (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (t - (p : ℤ)))).obj F) J ≫
        koszulCoordinateMul R ι F t p i ≫ koszulTwistInv R ι F t p =
      koszulMul R ι F i (t - (p : ℤ)) (t + 1 - (p : ℤ)) (koszulDeg_shift t p) ≫
        twistMergeInv R ι ((1 : ℕ) : ℤ) (t - (p : ℤ)) (t + 1 - (p : ℤ)) (koszulDeg_shift t p) F ≫
          twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ Sigma.ι (fun _ : KoszulIndex ι p =>
            (moduleTensorLeftFunctor (ProjectiveSpace R ι)
              (twistingSheaf R ι (t - (p : ℤ)))).obj F) J := by
  rw [koszulCoordinateMul, Sigma.ι_comp_desc_assoc, Category.assoc, ι_koszulTwistInv]

omit [LinearOrder ι] in
/-- Multiplication by `Xᵢ` on a Koszul term is the coordinate multiplication between Koszul terms
of adjacent twists, followed by `koszulTwistInv`. -/
theorem unitMultiply_koszulTerm (t : ℤ) (p : ℕ) (i : ι) :
    unitMultiply (coordinateUnitHom R ι i) (koszulTerm R ι F t p) =
      koszulCoordinateMul R ι F t p i ≫ koszulTwistInv R ι F t p :=
  Sigma.hom_ext _ _ fun J => (ι_unitMultiply_koszulTerm R ι F t p i J).trans
    (ι_koszulCoordinateMul_twistInv R ι F t p i J).symm

/-- `koszulTwistInv` commutes with the contractions. -/
theorem koszulContraction_comp_twistInv (t : ℤ) (p : ℕ) (i : ι) :
    koszulContraction R ι F (t + 1) p i ≫ koszulTwistInv R ι F t p =
      koszulTwistInv R ι F t (p + 1) ≫
        twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ koszulContraction R ι F t p i := by
  apply Sigma.hom_ext
  intro J
  rw [ι_koszulTwistInv_assoc, ← MonoidalCategory.whiskerLeft_comp]
  by_cases hi : i ∈ J.1
  · rw [← Category.assoc,
      ι_koszulContraction_of_mem R ι F (t + 1) p i J (koszulIndexErase J i hi) hi rfl,
      ι_koszulContraction_of_mem R ι F t p i J (koszulIndexErase J i hi) hi rfl,
      Preadditive.zsmul_comp, Category.assoc, ι_koszulTwistInv, moduleWhiskerLeft_zsmul,
      Preadditive.comp_zsmul, MonoidalCategory.whiskerLeft_comp]
    congr 1
    rw [← Category.assoc, multiplyTo_comp_twistMergeInv R ι ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
      (t - ((p + 1 : ℕ) : ℤ)) (t - (p : ℤ)) (t + 1 - ((p + 1 : ℕ) : ℤ)) (t + 1 - (p : ℤ))
      (koszulDeg_contraction t p) (koszulDeg_shift t (p + 1)) (koszulDeg_shift t p)
      (koszulDeg_contraction (t + 1) p) (coordinateSection R ι i) F, Category.assoc]
  · rw [← Category.assoc, ι_koszulContraction_of_notMem R ι F (t + 1) p i J hi,
      ι_koszulContraction_of_notMem R ι F t p i J hi, zero_comp,
      MonoidalPreadditive.whiskerLeft_zero, comp_zero]

/-- `koszulTwistInv` commutes with the Koszul differentials. -/
theorem koszulDifferential_comp_twistInv (t : ℤ) (p : ℕ) :
    koszulDifferential R ι F (t + 1) p ≫ koszulTwistInv R ι F t p =
      koszulTwistInv R ι F t (p + 1) ≫
        twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ koszulDifferential R ι F t p := by
  simp only [koszulDifferential, Preadditive.sum_comp, whiskerLeft_sum,
    Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun i _ => koszulContraction_comp_twistInv R ι F t p i

/-! ### Exactness of the Koszul complex -/

/-- In degree zero the wedge alone is a null-homotopy: `h ≫ d = Xᵢ`, that is `d ∘ h = Xᵢ`,
on `K_0`. -/
theorem koszul_homotopy_zero (t : ℤ) (i : ι) :
    koszulWedge R ι F t 0 i ≫ koszulDifferential R ι F (t + 1) 0 =
      koszulCoordinateMul R ι F t 0 i := by
  apply Sigma.hom_ext
  intro J
  have hJ : J.1 = ∅ := Finset.card_eq_zero.mp J.2
  have hi : i ∉ J.1 := by rw [hJ]; exact Finset.notMem_empty i
  rw [koszulCoordinateMul, Sigma.ι_comp_desc, ← Category.assoc,
    ι_koszulWedge_of_notMem R ι F t 0 i J (koszulIndexInsert J i hi) hi rfl,
    Preadditive.zsmul_comp, Category.assoc]
  simp only [koszulDifferential, Preadditive.comp_sum]
  rw [Finset.sum_eq_single i]
  · rw [ι_koszulContraction_of_mem R ι F (t + 1) 0 i (koszulIndexInsert J i hi) J
        (Finset.mem_insert_self i J.1) (Finset.erase_insert hi).symm,
      Preadditive.comp_zsmul, smul_smul, ← Category.assoc,
      eqToHom_comp_koszulMul R ι F i (koszulDeg_wedge t 0) (koszulWedgeEq R ι F t 0)
        (t + 1 - ((0 : ℕ) : ℤ))
        (koszulDeg_contraction (t + 1) 0) (koszulDeg_shift t 0)]
    rw [show koszulSign i (insert i J.1) = koszulSign i J.1 from koszulSign_insert_self i J.1,
      koszulSign_mul_self, one_smul]
  · intro j _ hji
    have hj : j ∉ (koszulIndexInsert J i hi).1 := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hji h
      · rw [hJ] at h
        exact Finset.notMem_empty j h
    rw [ι_koszulContraction_of_notMem R ι F (t + 1) 0 j _ hj, comp_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [LinearOrder ι] [Fintype ι] in
/-- A morphism `f : A ⟶ Z` is an epimorphism when multiplication by every coordinate on `Z`
factors through `O(1) ◁ f`: its cokernel is killed by every coordinate. -/
theorem epi_of_unitMultiply_factor {A Z : (ProjectiveSpace R ι).Modules} (f : A ⟶ Z)
    (hf : ∀ i, ∃ g : Z ⟶ twistingSheaf R ι ((1 : ℕ) : ℤ) ⊗ A,
      unitMultiply (coordinateUnitHom R ι i) Z = g ≫ twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ f) :
    Epi f := by
  apply Preadditive.epi_of_isZero_cokernel
  apply isZero_of_unitMultiply_coordinate_eq_zero R ι
  intro i
  obtain ⟨g, hg⟩ := hf i
  rw [← cancel_epi (cokernel.π f), comp_zero, unitMultiply_naturality, hg, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, cokernel.condition, MonoidalPreadditive.whiskerLeft_zero,
    comp_zero]

/-- The last Koszul differential `K_1 ⟶ K_0` is an epimorphism. -/
theorem epi_koszulDifferential_zero (t : ℤ) : Epi (koszulDifferential R ι F t 0) := by
  apply epi_of_unitMultiply_factor R ι
  intro i
  refine ⟨koszulWedge R ι F t 0 i ≫ koszulTwistInv R ι F t (0 + 1), ?_⟩
  rw [unitMultiply_koszulTerm, ← koszul_homotopy_zero, Category.assoc,
    koszulDifferential_comp_twistInv, Category.assoc]

/-- The Koszul complex is exact at `K_{p+1}`: the differential `K_{p+2} ⟶ K_{p+1}` maps onto the
kernel of `K_{p+1} ⟶ K_p`. -/
theorem epi_koszul_kernelLift (t : ℤ) (p : ℕ) :
    Epi (kernel.lift (koszulDifferential R ι F t p) (koszulDifferential R ι F t (p + 1))
      (koszulDifferential_comp R ι F t p)) := by
  apply epi_of_unitMultiply_factor R ι
  intro i
  refine ⟨kernel.ι (koszulDifferential R ι F t p) ≫ koszulWedge R ι F t (p + 1) i ≫
    koszulTwistInv R ι F t (p + 1 + 1), ?_⟩
  have h1 : kernel.ι (koszulDifferential R ι F t p) ≫ koszulCoordinateMul R ι F t (p + 1) i =
      kernel.ι (koszulDifferential R ι F t p) ≫ koszulWedge R ι F t (p + 1) i ≫
        koszulDifferential R ι F (t + 1) (p + 1) := by
    rw [← koszul_homotopy R ι F t p i, Preadditive.comp_add, kernel.condition_assoc, zero_comp,
      add_zero]
  have h2 : twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ koszulDifferential R ι F t (p + 1) =
      twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ kernel.lift (koszulDifferential R ι F t p)
        (koszulDifferential R ι F t (p + 1)) (koszulDifferential_comp R ι F t p) ≫
        twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ kernel.ι (koszulDifferential R ι F t p) := by
    rw [← MonoidalCategory.whiskerLeft_comp, kernel.lift_ι]
  rw [← cancel_mono (twistingSheaf R ι ((1 : ℕ) : ℤ) ◁ kernel.ι (koszulDifferential R ι F t p)),
    ← unitMultiply_naturality, unitMultiply_koszulTerm, ← Category.assoc, h1, Category.assoc,
    Category.assoc, koszulDifferential_comp_twistInv, h2]
  simp only [Category.assoc]

end AlgebraicGeometry.ProjectiveSpace
