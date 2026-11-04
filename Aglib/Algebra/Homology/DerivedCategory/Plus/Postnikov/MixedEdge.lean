/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangle
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Unit
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! # The actual negative-one shift and mixed connecting square

The original first two coefficient squares and native t-structure bounds
force the third square. The normalized negative-one triangle keeps the
original first two arrows positive and the original connecting arrow negative.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated.TStructure

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- A source upper bound and target lower bound force the actual third square. -/
theorem triangle_comm_three_of_first_two (t : TStructure D)
    {T U : Triangle D} (hT : T ∈ distTriang D) (hU : U ∈ distTriang D)
    (a : T.obj₁ ⟶ U.obj₁) (b : T.obj₂ ⟶ U.obj₂) (c : T.obj₃ ⟶ U.obj₃)
    (h₁ : T.mor₁ ≫ b = a ≫ U.mor₁)
    (h₂ : T.mor₂ ≫ c = b ≫ U.mor₂)
    (n : ℤ) (hA : t.IsLE T.obj₁ n) (hC : t.IsGE U.obj₃ n) :
    T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ U.mor₃ := by
  let : t.IsLE T.obj₁ n := hA
  let : t.IsGE U.obj₃ n := hC
  obtain ⟨c', hc₂, hc₃⟩ :=
    complete_distinguished_triangle_morphism T U hT hU a b h₁
  have hz : T.mor₂ ≫ (c' - c) = 0 := by
    rw [Preadditive.comp_sub, hc₂, h₂, sub_self]
  obtain ⟨d, hd⟩ := T.yoneda_exact₃ hT (c' - c) hz
  have hd₀ : d = 0 := t.zero_of_isLE_of_isGE d (n - 1) n (by omega)
    (t.isLE_shift T.obj₁ n 1 (n - 1) (by omega)) hC
  have hc : c' = c := sub_eq_zero.mp (hd.trans (by rw [hd₀, comp_zero]))
  exact hc₃.trans (congrArg (fun z => z ≫ U.mor₃) hc)

end CategoryTheory.Triangulated.TStructure

namespace CategoryTheory.Pretriangulated.Triangle

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- The original negative-one shift with its first two arrows kept positive. -/
def normalizedNegativeShift (T : Triangle D) : Triangle D :=
  Triangle.mk (T.mor₁⟦(-1 : ℤ)⟧') (T.mor₂⟦(-1 : ℤ)⟧')
    (-T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftFunctorComm D 1 (-1)).hom.app T.obj₁)

/-- The unchanged shifted objects are compared by `(1,-1,1)`. -/
def normalizedNegativeShiftIso (T : Triangle D) :
    (CategoryTheory.shiftFunctor (Triangle D) (-1 : ℤ)).obj T ≅
      normalizedNegativeShift T := by
  let e : ((CategoryTheory.shiftFunctor D (-1 : ℤ)).obj T.obj₂) ≅
      ((CategoryTheory.shiftFunctor D (-1 : ℤ)).obj T.obj₂) :=
    { hom := -𝟙 _, inv := -𝟙 _, hom_inv_id := by simp, inv_hom_id := by simp }
  refine Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_
  · change ((-1 : ℤ).negOnePow • T.mor₁⟦(-1 : ℤ)⟧') ≫ (-𝟙 _) =
      𝟙 _ ≫ T.mor₁⟦(-1 : ℤ)⟧'
    simp
  · change ((-1 : ℤ).negOnePow • T.mor₂⟦(-1 : ℤ)⟧') ≫ 𝟙 _ =
      (-𝟙 _) ≫ T.mor₂⟦(-1 : ℤ)⟧'
    simp
  · simp [normalizedNegativeShift, CategoryTheory.Pretriangulated.Triangle.shiftFunctor_eq,
      Triangle.shiftFunctor]


/-- This normalization is a distinguished triangle on the original objects. -/
theorem normalizedNegativeShift_distinguished (T : Triangle D) (hT : T ∈ distTriang D) :
    normalizedNegativeShift T ∈ distTriang D :=
  isomorphic_distinguished _ (shift_distinguished T hT (-1)) _
    (normalizedNegativeShiftIso T).symm

end CategoryTheory.Pretriangulated.Triangle

namespace DerivedCategory.Plus

universe w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The existing homology-normalized single comparison is natural in the bounded-below category. -/
theorem isoSingleHomology_naturality (n : ℤ) {K L : Plus C}
    [K.IsGE n] [K.IsLE n] [L.IsGE n] [L.IsLE n] (f : K ⟶ L) :
    f ≫ (isoSingleHomology L n).hom =
      (isoSingleHomology K n).hom ≫ (singleFunctor C n).map
        ((homologyFunctor C n).map f) := by
  apply (ι : Plus C ⥤ DerivedCategory C).map_injective
  simp only [Functor.map_comp, ι_map_isoSingleHomology_hom]
  exact DerivedCategory.isoSingleHomology_naturality n (ι.map f)

/-- The actual top-homology projection, using native truncation and its original homology map. -/
def upperHomologyProjection (K : Plus C) (n : ℤ) [K.IsLE n] :
    K ⟶ (singleFunctor C n).obj ((homologyFunctor C n).obj K) :=
  (TStructure.t.truncGEπ n).app K ≫
    (isoSingleHomology ((TStructure.t.truncGE n).obj K) n).hom ≫
      (singleFunctor C n).map (homologyTruncGEIso K n n (by rfl)).inv

/-- The top projection induces the identity on the original top homology. -/
theorem upperHomologyProjection_homology (K : Plus C) (n : ℤ) [K.IsLE n] :
    (homologyFunctor C n).map (upperHomologyProjection K n) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app
        ((homologyFunctor C n).obj K) = 𝟙 _ := by
  let H := homologyFunctor C n
  let T := (TStructure.t.truncGE n).obj K
  let e := homologyTruncGEIso K n n le_rfl
  let a := isoSingleHomology T n
  let v := DerivedCategory.singleFunctorCompHomologyFunctorIso C n
  have ha : H.map a.hom ≫ v.hom.app (H.obj T) = 𝟙 (H.obj T) := by
    change (DerivedCategory.homologyFunctor C n).map ((ι : Plus C ⥤ _).map a.hom) ≫
      v.hom.app (H.obj T) = 𝟙 (H.obj T)
    rw [ι_map_isoSingleHomology_hom]
    exact DerivedCategory.isoSingleHomology_homology ((ι : Plus C ⥤ _).obj T) n
  have hn : H.map ((singleFunctor C n).map e.inv) ≫ v.hom.app (H.obj K) =
      v.hom.app (H.obj T) ≫ e.inv := v.hom.naturality e.inv
  change H.map ((TStructure.t.truncGEπ n).app K ≫ a.hom ≫
    (singleFunctor C n).map e.inv) ≫ v.hom.app (H.obj K) = 𝟙 (H.obj K)
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, ← Category.assoc (H.map a.hom), ha, Category.id_comp]
  exact e.hom_inv_id

/-- Naturality retains the actual top-homology projection on both objects. -/
theorem upperHomologyProjection_naturality (n : ℤ) {K L : Plus C}
    [K.IsLE n] [L.IsLE n] (f : K ⟶ L) :
    f ≫ upperHomologyProjection L n =
      upperHomologyProjection K n ≫ (singleFunctor C n).map
        ((homologyFunctor C n).map f) := by
  let H := homologyFunctor C n
  let S := singleFunctor C n
  let eK := homologyTruncGEIso K n n (by rfl)
  let eL := homologyTruncGEIso L n n (by rfl)
  have hh : eK.hom ≫ H.map ((TStructure.t.truncGE n).map f) = H.map f ≫ eL.hom := by
    exact (H.map_comp _ _).symm.trans
      ((congrArg H.map (TStructure.t.truncGEπ_naturality n f)).trans (H.map_comp _ _))
  have hi : H.map ((TStructure.t.truncGE n).map f) ≫ eL.inv = eK.inv ≫ H.map f := by
    apply (cancel_epi eK.hom).mp
    rw [← Category.assoc, hh]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  dsimp only [upperHomologyProjection]
  rw [← Category.assoc f, ← TStructure.t.truncGEπ_naturality n f, Category.assoc,
    ← Category.assoc ((TStructure.t.truncGE n).map f),
    isoSingleHomology_naturality n ((TStructure.t.truncGE n).map f)]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun z => (TStructure.t.truncGEπ n).app K ≫
    (isoSingleHomology ((TStructure.t.truncGE n).obj K) n).hom ≫ S.map z) hi

/-- The actual top degree-one map expressed with the original degree-zero single shifted by -1. -/
def upperHomologyShiftMap (K : Plus C) [K.IsLE 1] {M : C}
    (a : (homologyFunctor C 1).obj K ⟶ M) :
    K ⟶ ((singleFunctor C 0).obj M)⟦(-1 : ℤ)⟧ :=
  upperHomologyProjection K 1 ≫ (singleFunctor C 1).map a ≫
    (((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app M).inv

/-- A square on actual degree-one homology supplies the corresponding
whole shifted-single square. -/
theorem upperHomologyShiftMap_comm {K L : Plus C} [K.IsLE 1] [L.IsLE 1]
    (f : K ⟶ L) {M N : C} (a : (homologyFunctor C 1).obj K ⟶ M)
    (b : (homologyFunctor C 1).obj L ⟶ N) (g : M ⟶ N)
    (h : (homologyFunctor C 1).map f ≫ b = a ≫ g) :
    f ≫ upperHomologyShiftMap L b =
      upperHomologyShiftMap K a ≫ ((singleFunctor C 0).map g)⟦(-1 : ℤ)⟧' := by
  let ζ := (singleFunctors C).shiftIso (-1) 1 0 (by omega)
  have hz : (singleFunctor C 1).map g ≫ (ζ.app N).inv =
      (ζ.app M).inv ≫ ((singleFunctor C 0).map g)⟦(-1 : ℤ)⟧' :=
    ζ.inv.naturality g
  calc
    _ = upperHomologyProjection K 1 ≫
        (singleFunctor C 1).map ((homologyFunctor C 1).map f ≫ b) ≫
          (ζ.app N).inv := by
      dsimp only [upperHomologyShiftMap]
      rw [← Category.assoc f, upperHomologyProjection_naturality 1 f]
      simp only [Category.assoc, Functor.map_comp]
      rfl
    _ = upperHomologyProjection K 1 ≫ (singleFunctor C 1).map (a ≫ g) ≫
          (ζ.app N).inv := by rw [h]
    _ = _ := by
      rw [Functor.map_comp]
      simpa only [upperHomologyShiftMap, Category.assoc, ζ] using
        congrArg (fun z => upperHomologyProjection K 1 ≫ (singleFunctor C 1).map a ≫ z) hz

/-- The native mixed connecting map is the negative shifted short-exact boundary.
Only the first two heart-level comparison squares are inputs; the third is proved by bounds. -/
theorem mixedEdge_negative_transgression
    (T : Triangle (Plus C)) (hT : T ∈ distTriang (Plus C))
    [T.obj₁.IsLE 1] [T.obj₂.IsLE 1] [T.obj₃.IsLE 1]
    {S : ShortComplex C} (hS : S.ShortExact)
    (a : (homologyFunctor C 1).obj T.obj₁ ⟶ S.X₁)
    (b : (homologyFunctor C 1).obj T.obj₂ ⟶ S.X₂)
    (c : (homologyFunctor C 1).obj T.obj₃ ⟶ S.X₃)
    (h₁ : (homologyFunctor C 1).map T.mor₁ ≫ b = a ≫ S.f)
    (h₂ : (homologyFunctor C 1).map T.mor₂ ≫ c = b ≫ S.g) :
    T.mor₃ ≫ (upperHomologyShiftMap T.obj₁ a)⟦(1 : ℤ)⟧' =
      -(upperHomologyShiftMap T.obj₃ c ≫
        hS.singleTrianglePlus.mor₃⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorComm (Plus C) 1 (-1)).hom.app
            ((singleFunctor C 0).obj S.X₁)) := by
  let U := Triangle.normalizedNegativeShift hS.singleTrianglePlus
  have hU : U ∈ distTriang (Plus C) :=
    Triangle.normalizedNegativeShift_distinguished _ hS.singleTrianglePlus_distinguished
  have hc : TStructure.t.IsGE U.obj₃ 1 := by
    change (((singleFunctor C 0).obj S.X₃)⟦(-1 : ℤ)⟧).IsGE 1
    exact TStructure.t.isGE_shift _ 0 (-1) 1 (by omega)
  have h := CategoryTheory.Triangulated.TStructure.triangle_comm_three_of_first_two
    TStructure.t hT hU
    (upperHomologyShiftMap T.obj₁ a) (upperHomologyShiftMap T.obj₂ b)
    (upperHomologyShiftMap T.obj₃ c)
    (upperHomologyShiftMap_comm T.mor₁ a b S.f h₁)
    (upperHomologyShiftMap_comm T.mor₂ b c S.g h₂)
    1 inferInstance hc
  change T.mor₃ ≫ (upperHomologyShiftMap T.obj₁ a)⟦(1 : ℤ)⟧' =
    upperHomologyShiftMap T.obj₃ c ≫
      (-hS.singleTrianglePlus.mor₃⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorComm (Plus C) 1 (-1)).hom.app
          ((singleFunctor C 0).obj S.X₁)) at h
  simpa only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] using h

/-- Surjectivity in degree zero and the source upper bound make the actual H1 row short exact. -/
theorem homologyOneShortComplex_shortExact_of_epi_zero
    (T : Triangle (Plus C)) (hT : T ∈ distTriang (Plus C)) [T.obj₁.IsLE 1]
    [Epi ((homologyFunctor C 0).map T.mor₂)] :
    (homologyOneShortComplex T hT).ShortExact := by
  let H := homologyFunctor C 0
  have hEpi : Epi ((H.shift (0 : ℤ)).map T.mor₂) := by
    let e := H.isoShiftZero ℤ
    have hw : (H.shift (0 : ℤ)).map T.mor₂ =
        e.hom.app T.obj₂ ≫ H.map T.mor₂ ≫ e.inv.app T.obj₃ := by
      calc
        _ = ((H.shift (0 : ℤ)).map T.mor₂ ≫ e.hom.app T.obj₃) ≫ e.inv.app T.obj₃ := by
          simp
        _ = _ := by rw [e.hom.naturality]; simp only [Category.assoc]
    rw [hw]
    infer_instance
  have hz : H.homologySequenceδ T 0 1 (by omega) = 0 :=
    (H.homologySequence_epi_shift_map_mor₂_iff T hT 0 1 (by omega)).mp hEpi
  have h₂ : IsZero ((homologyFunctor C 2).obj T.obj₁) :=
    isZero_homology_of_isLE T.obj₁ 1 2 (by omega)
  refine { exact := H.homologySequence_exact₂ T hT 1, mono_f := ?_, epi_g := ?_ }
  · exact (H.homologySequence_mono_shift_map_mor₁_iff T hT 0 1 (by omega)).mpr hz
  · exact (H.homologySequence_epi_shift_map_mor₂_iff T hT 1 2 (by omega)).mpr
      (h₂.eq_of_tgt _ _)

/-- The original H1 short exact row supplies its own negative transgression,
without an externally supplied triangle comparison or homology identification. -/
theorem mixedEdge_negative_transgression_homology
    (T : Triangle (Plus C)) (hT : T ∈ distTriang (Plus C))
    [T.obj₁.IsLE 1] [T.obj₂.IsLE 1] [T.obj₃.IsLE 1]
    [Epi ((homologyFunctor C 0).map T.mor₂)] :
    let hS := homologyOneShortComplex_shortExact_of_epi_zero T hT
    T.mor₃ ≫ (upperHomologyShiftMap T.obj₁ (𝟙 _))⟦(1 : ℤ)⟧' =
      -(upperHomologyShiftMap T.obj₃ (𝟙 _) ≫
        hS.singleTrianglePlus.mor₃⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorComm (Plus C) 1 (-1)).hom.app
            ((singleFunctor C 0).obj ((homologyFunctor C 1).obj T.obj₁))) := by
  dsimp only
  apply mixedEdge_negative_transgression T hT
    (homologyOneShortComplex_shortExact_of_epi_zero T hT) (𝟙 _) (𝟙 _) (𝟙 _)
  · simp [homologyOneShortComplex]
  · simp [homologyOneShortComplex]

end DerivedCategory.Plus

namespace DerivedCategory.Plus

universe uValue vValue wValue
variable {C : Type uValue} [Category.{vValue} C] [Abelian C] [HasDerivedCategory.{wValue} C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An original degree-q single map is normalized by its actual top homology value. -/
theorem upperHomologyProjection_comp_eq_id_of_value
    (q : ℤ) (U : C) (K : Plus C) [K.IsLE q]
    (x : (singleFunctor C q).obj U ⟶ K)
    (a : (homologyFunctor C q).obj K ⟶ U)
    (hx : (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app U ≫
      (homologyFunctor C q).map x ≫ a = 𝟙 U) :
    x ≫ upperHomologyProjection K q ≫ (singleFunctor C q).map a =
      𝟙 ((singleFunctor C q).obj U) := by
  let H := homologyFunctor C q
  let e : singleFunctor C q ⋙ H ≅ 𝟭 C := singleFunctorCompHomologyFunctorIso q
  have hx' : H.map x ≫ a = e.hom.app U := by
    apply (cancel_epi (e.inv.app U)).mp
    rw [Iso.inv_hom_id_app]
    dsimp only [e, H, singleFunctorCompHomologyFunctorIso]
    exact hx
  have h : H.map (x ≫ upperHomologyProjection K q ≫ (singleFunctor C q).map a) ≫
      e.hom.app U = e.hom.app U := by
    rw [H.map_comp, H.map_comp]
    simp only [Category.assoc]
    have hn := e.hom.naturality a
    change H.map ((singleFunctor C q).map a) ≫ e.hom.app U =
      e.hom.app (H.obj K) ≫ a at hn
    have hp := upperHomologyProjection_homology K q
    change H.map (upperHomologyProjection K q) ≫ e.hom.app (H.obj K) = 𝟙 _ at hp
    rw [hn, ← Category.assoc (H.map (upperHomologyProjection K q)), hp, Category.id_comp]
    exact hx'
  apply (ι : Plus C ⥤ DerivedCategory C).map_injective
  apply DerivedCategory.homology_map_injective_of_isGE_of_isLE _ _ q
  change H.map (x ≫ upperHomologyProjection K q ≫ (singleFunctor C q).map a) = H.map (𝟙 _)
  apply (cancel_mono (e.hom.app U)).mp
  simpa only [H.map_id, Category.id_comp] using h

end DerivedCategory.Plus

namespace DerivedCategory.Plus

universe uValue vValue wValue

variable {C : Type uValue} [Category.{vValue} C] [Abelian C] [HasDerivedCategory.{wValue} C]

/-- A map from a degree-one single retains its actual first homology value
under the original top projection. -/
theorem upperHomologyShiftMap_from_single {K : Plus C} [K.IsLE 1] {U V : C}
    (x : (singleFunctor C 1).obj U ⟶ K)
    (a : (homologyFunctor C 1).obj K ⟶ V) (f : U ⟶ V)
    (hx : (homologyFunctor C 1).map x ≫ a =
      (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app U ≫ f) :
    x ≫ upperHomologyShiftMap K a =
      (singleFunctor C 1).map f ≫
        (((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app V).inv := by
  let F := singleFunctor C 1
  let H := homologyFunctor C 1
  let e := (singleFunctorCompHomologyFunctorIso (C := C) 1).app U
  let S := F.obj U
  let η := ((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app V
  have h₀ : upperHomologyProjection S 1 ≫ F.map e.hom = 𝟙 S := by
    have h : 𝟙 S ≫ (upperHomologyProjection S 1 ≫ F.map e.hom) = 𝟙 S :=
      upperHomologyProjection_comp_eq_id_of_value 1 U S (𝟙 S) e.hom
      (by
        change e.inv ≫ H.map (𝟙 S) ≫ e.hom = 𝟙 U
        calc
          _ = e.inv ≫ (𝟙 (H.obj S)) ≫ e.hom :=
            congrArg (fun (z : H.obj S ⟶ H.obj S) => e.inv ≫ z ≫ e.hom) (H.map_id S)
          _ = e.inv ≫ e.hom := congrArg (fun z => e.inv ≫ z) (Category.id_comp e.hom)
          _ = _ := e.inv_hom_id)
    exact (Category.id_comp _).symm.trans h
  have hx' : H.map x ≫ a = e.hom ≫ f := hx
  have h : x ≫ upperHomologyProjection K 1 = upperHomologyProjection S 1 ≫ F.map (H.map x) :=
    upperHomologyProjection_naturality 1 x
  change x ≫ upperHomologyProjection K 1 ≫ F.map a ≫ η.inv = F.map f ≫ η.inv
  calc
    _ = upperHomologyProjection S 1 ≫ F.map (H.map x ≫ a) ≫ η.inv := by
      rw [← Category.assoc x, h, F.map_comp]
      simp only [Category.assoc]
    _ = upperHomologyProjection S 1 ≫ F.map (e.hom ≫ f) ≫ η.inv :=
      congrArg (fun z => upperHomologyProjection S 1 ≫ F.map z ≫ η.inv) hx'
    _ = (upperHomologyProjection S 1 ≫ F.map e.hom) ≫ F.map f ≫ η.inv := by
      rw [F.map_comp]
      simp only [Category.assoc]
    _ = _ := by rw [h₀, Category.id_comp]

/-- The original mixed connecting map evaluates a degree-one class by the
negative shifted original boundary of its actual first homology value. -/
theorem mixedEdge_precomp_topSingle
    (T : Triangle (Plus C)) (hT : T ∈ distTriang (Plus C))
    [T.obj₁.IsLE 1] [T.obj₂.IsLE 1] [T.obj₃.IsLE 1]
    {S : ShortComplex C} (hS : S.ShortExact)
    (a : (homologyFunctor C 1).obj T.obj₁ ⟶ S.X₁)
    (b : (homologyFunctor C 1).obj T.obj₂ ⟶ S.X₂)
    (c : (homologyFunctor C 1).obj T.obj₃ ⟶ S.X₃)
    (h₁ : (homologyFunctor C 1).map T.mor₁ ≫ b = a ≫ S.f)
    (h₂ : (homologyFunctor C 1).map T.mor₂ ≫ c = b ≫ S.g)
    {W : C} (x : (singleFunctor C 1).obj W ⟶ T.obj₃) (j : W ⟶ S.X₃)
    (hx : (homologyFunctor C 1).map x ≫ c =
      (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app W ≫ j) :
    x ≫ T.mor₃ ≫ (upperHomologyShiftMap T.obj₁ a)⟦(1 : ℤ)⟧' =
      -((singleFunctor C 1).map j ≫
        (((singleFunctors C).shiftIso (-1) 1 0 (by omega)).app S.X₃).inv ≫
        hS.singleTrianglePlus.mor₃⟦(-1 : ℤ)⟧' ≫
          (shiftFunctorComm (Plus C) 1 (-1)).hom.app
            ((singleFunctor C 0).obj S.X₁)) := by
  rw [mixedEdge_negative_transgression T hT hS a b c h₁ h₂, Preadditive.comp_neg,
    ← Category.assoc x, upperHomologyShiftMap_from_single x c j hx, Category.assoc]

end DerivedCategory.Plus

namespace CategoryTheory

variable {D : Type*} [Category* D] [HasShift D ℤ]

/-- Interchanging opposite shifts and then cancelling gives the original cancellation. -/
private theorem shiftFunctorComm_comp_shiftFunctorCompIsoId (q : ℤ) (K : D) :
    (shiftFunctorComm D q (-q)).hom.app K ≫
      (shiftFunctorCompIsoId D (-q) q (neg_add_cancel q)).hom.app K =
    (shiftFunctorCompIsoId D q (-q) (add_neg_cancel q)).hom.app K := by
  rw [shiftFunctorComm_eq D q (-q) 0 (add_neg_cancel q)]
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Undo the negative shift of the original connecting arrow using the
original inverse shift adjunct. -/
private theorem inverseShiftAdjunct_comp_shiftFunctorComm {U V K : D}
    (q : ℤ) (a : U ⟶ V) (b : ShiftedHom V K q) :
    let e : shiftFunctor D (-q) ⊣ shiftFunctor D q :=
      (shiftEquiv' D (-q) q (neg_add_cancel q)).toAdjunction
    (e.homEquiv U K).symm (a ≫ b) =
      a⟦-q⟧' ≫ b⟦-q⟧' ≫ (shiftFunctorComm D q (-q)).hom.app K ≫
        (shiftFunctorCompIsoId D (-q) q (neg_add_cancel q)).hom.app K := by
  intro e
  rw [e.homEquiv_counit, Functor.map_comp, Category.assoc,
    shiftFunctorComm_comp_shiftFunctorCompIsoId]
  rfl

end CategoryTheory

namespace DerivedCategory.Plus

universe uValue vValue wValue

variable {C : Type uValue} [Category.{vValue} C] [Abelian C] [HasDerivedCategory.{wValue} C]

/-- With both original shift cancellations, the mixed connecting map is
the negative inverse adjunct of the original short exact boundary. -/
theorem mixedEdge_precomp_topSingle_inverseAdjunct
    (T : Triangle (Plus C)) (hT : T ∈ distTriang (Plus C))
    [T.obj₁.IsLE 1] [T.obj₂.IsLE 1] [T.obj₃.IsLE 1]
    {S : ShortComplex C} (hS : S.ShortExact)
    (a : (homologyFunctor C 1).obj T.obj₁ ⟶ S.X₁)
    (b : (homologyFunctor C 1).obj T.obj₂ ⟶ S.X₂)
    (c : (homologyFunctor C 1).obj T.obj₃ ⟶ S.X₃)
    (h₁ : (homologyFunctor C 1).map T.mor₁ ≫ b = a ≫ S.f)
    (h₂ : (homologyFunctor C 1).map T.mor₂ ≫ c = b ≫ S.g)
    {W : C} (x : (singleFunctor C 1).obj W ⟶ T.obj₃) (j : W ⟶ S.X₃)
    (hx : (homologyFunctor C 1).map x ≫ c =
      (singleFunctorCompHomologyFunctorIso (C := C) 1).hom.app W ≫ j) :
    let U := (singleFunctor C 0).obj W
    let K := (singleFunctor C 0).obj S.X₁
    let η := (singleFunctors C).shiftIso (-1) 1 0 (by omega)
    let adj : shiftFunctor (Plus C) (-1 : ℤ) ⊣ shiftFunctor (Plus C) (1 : ℤ) :=
      (shiftEquiv' (Plus C) (-1 : ℤ) 1 (by omega)).toAdjunction
    η.hom.app W ≫ x ≫ T.mor₃ ≫ (upperHomologyShiftMap T.obj₁ a)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId (Plus C) (-1 : ℤ) 1 (by omega)).hom.app K =
    -((adj.homEquiv U K).symm ((singleFunctor C 0).map j ≫ hS.singleTrianglePlus.mor₃)) := by
  intro U K η adj
  let z : ShiftedHom ((singleFunctor C 0).obj S.X₃) K (1 : ℤ) :=
    hS.singleTrianglePlus.mor₃
  let μ := shiftFunctorCompIsoId (Plus C) (-1 : ℤ) 1 (by omega)
  let ν := shiftFunctorComm (Plus C) (1 : ℤ) (-1)
  let F := singleFunctor C 0
  let G := singleFunctor C 1
  have hj : η.hom.app W ≫ G.map j ≫ η.inv.app S.X₃ = (F.map j)⟦(-1 : ℤ)⟧' := by
    have h : (F.map j)⟦(-1 : ℤ)⟧' ≫ η.hom.app S.X₃ = η.hom.app W ≫ G.map j :=
      η.hom.naturality j
    apply (cancel_mono (η.hom.app S.X₃)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact (congrArg (fun f => η.hom.app W ≫ f) (Category.comp_id (G.map j))).trans h.symm
  have h : x ≫ T.mor₃ ≫ (upperHomologyShiftMap T.obj₁ a)⟦(1 : ℤ)⟧' =
      -(G.map j ≫ η.inv.app S.X₃ ≫ z⟦(-1 : ℤ)⟧' ≫ ν.hom.app K) :=
    mixedEdge_precomp_topSingle T hT hS a b c h₁ h₂ x j hx
  have h' := congrArg (fun w => η.hom.app W ≫ w ≫ μ.hom.app K) h
  change η.hom.app W ≫ x ≫ T.mor₃ ≫ (upperHomologyShiftMap T.obj₁ a)⟦(1 : ℤ)⟧' ≫
    μ.hom.app K = _
  calc
    _ = -((η.hom.app W ≫ G.map j ≫ η.inv.app S.X₃) ≫ z⟦(-1 : ℤ)⟧' ≫
        ν.hom.app K ≫ μ.hom.app K) := by
      have hc : (z⟦(-1 : ℤ)⟧' ≫ ν.hom.app K) ≫ μ.hom.app K =
          z⟦(-1 : ℤ)⟧' ≫ ν.hom.app K ≫ μ.hom.app K := Category.assoc _ _ _
      have ht : η.hom.app W ≫ x ≫ T.mor₃ ≫ (upperHomologyShiftMap T.obj₁ a)⟦(1 : ℤ)⟧' ≫
          μ.hom.app K =
        -η.hom.app W ≫ G.map j ≫ η.inv.app S.X₃ ≫
          (z⟦(-1 : ℤ)⟧' ≫ ν.hom.app K) ≫ μ.hom.app K := by
        simpa only [Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg] using h'
      rw [ht, hc]
      simp only [Category.assoc]
    _ = -((F.map j)⟦(-1 : ℤ)⟧' ≫ z⟦(-1 : ℤ)⟧' ≫
        ν.hom.app K ≫ μ.hom.app K) :=
      congrArg (fun k => -(k ≫ z⟦(-1 : ℤ)⟧' ≫ ν.hom.app K ≫ μ.hom.app K)) hj
    _ = _ := congrArg Neg.neg (inverseShiftAdjunct_comp_shiftFunctorComm (1 : ℤ) (F.map j) z).symm

end DerivedCategory.Plus
