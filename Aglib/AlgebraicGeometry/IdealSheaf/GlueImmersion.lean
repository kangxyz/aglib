/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.Limits.Monomorphisms
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Gluing immersions that represent a Zariski-local condition

Let `X` be a locally Noetherian scheme and `P` a condition on morphisms `g : T ⟶ X` from locally
Noetherian schemes, stable under restriction to open subschemes of `T` and local on `T`. Suppose
that near every point of `X` the condition is represented by an immersion: every `x : X` has an
open neighbourhood `U` and an immersion `m : Z ⟶ X` with image in `U` such that a morphism `g`
with image in `U` satisfies `P` exactly when it factors through `m`. Then `P` is represented by
one immersion `Z ⟶ X` (`Scheme.exists_isImmersion_forall_exists_lift_iff`).

The construction:

* each local immersion `m_i` is closed in the open `O_i = coborder (range m_i) ∩ U_i`
  (`Scheme.Hom.coborderRange`), through the closed immersion `glueImmersionLift hm i`;
* the kernels of these closed immersions agree on the overlaps of the `O_i`
  (`comap_ker_glueImmersionLift_le`): two closed subschemes of an overlap that represent the
  condition on locally Noetherian schemes factor through each other, and the closed subschemes are
  themselves locally Noetherian;
* they glue (`IdealSheafData.glue`) to an ideal sheaf on `O = ⋃ O_i`, whose closed subscheme,
  followed by the inclusion of `O`, is the required immersion (`glueImmersion`).

`exists_lift_iff_comap_ker_eq_bot` states the factorization criterion used throughout: a morphism
`k` factors through a closed immersion `c` if and only if the kernel of `c` pulls back to zero
along `k`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- **Factorization through a closed immersion.** A morphism `k` factors through a closed
immersion `c` if and only if the kernel of `c` pulls back to zero along `k`. -/
theorem exists_lift_iff_comap_ker_eq_bot {Z Y W : Scheme.{u}} (c : Z ⟶ Y) [IsClosedImmersion c]
    (k : W ⟶ Y) : (∃ a : W ⟶ Z, a ≫ c = k) ↔ c.ker.comap k = ⊥ := by
  constructor
  · rintro ⟨a, rfl⟩
    have hc : c.ker.comap c = ⊥ :=
      le_bot_iff.mp ((IdealSheafData.map_gc c c.ker ⊥).mpr (IdealSheafData.map_bot c).ge)
    rw [IdealSheafData.comap_comp, hc, IdealSheafData.comap_bot]
  · intro h
    have H : c.ker ≤ k.ker := by
      rw [← IdealSheafData.map_bot k]
      exact (IdealSheafData.map_gc k c.ker ⊥).mp h.le
    exact ⟨IsClosedImmersion.lift c k H, IsClosedImmersion.lift_fac c k H⟩

section Glue

variable {X : Scheme.{u}} {κ : Type u} (U : κ → X.Opens) {Z : κ → Scheme.{u}}
  (m : ∀ i, Z i ⟶ X) [∀ i, IsImmersion (m i)]

/-- The open `coborder (range m_i) ∩ U_i` of `X`, in which the image of `m_i` is closed. -/
def glueImmersionOpen (i : κ) : X.Opens :=
  (m i).coborderRange ⊓ U i

/-- The union of the opens `glueImmersionOpen U m i`. -/
def glueImmersionUnion : X.Opens :=
  ⨆ i, glueImmersionOpen U m i

theorem le_glueImmersionUnion (i : κ) : glueImmersionOpen U m i ≤ glueImmersionUnion U m :=
  le_iSup (glueImmersionOpen U m) i

/-- The inclusion of `glueImmersionOpen U m i` into the union `glueImmersionUnion U m`. -/
abbrev glueImmersionIncl (i : κ) :
    (glueImmersionOpen U m i).toScheme ⟶ (glueImmersionUnion U m).toScheme :=
  X.homOfLE (le_glueImmersionUnion U m i)

@[reassoc]
theorem glueImmersionIncl_ι (i : κ) :
    glueImmersionIncl U m i ≫ (glueImmersionUnion U m).ι = (glueImmersionOpen U m i).ι :=
  Scheme.homOfLE_ι _ _

/-- The opens `glueImmersionOpen U m i` cover their union. -/
theorem exists_glueImmersionIncl_eq (x : (glueImmersionUnion U m).toScheme) :
    ∃ i y, glueImmersionIncl U m i y = x := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
  exact ⟨i, ⟨x.1, hi⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩

variable {U m} (hm : ∀ i, Set.range (m i) ⊆ U i)

/-- The lift of `m_i` to the open `glueImmersionOpen U m i`, a closed immersion. -/
def glueImmersionLift (i : κ) : Z i ⟶ (glueImmersionOpen U m i).toScheme :=
  IsOpenImmersion.lift (glueImmersionOpen U m i).ι (m i) (by
    rw [Scheme.Opens.range_ι, glueImmersionOpen, Opens.coe_inf]
    exact Set.subset_inter subset_coborder (hm i))

@[reassoc (attr := simp)]
theorem glueImmersionLift_ι (i : κ) :
    glueImmersionLift hm i ≫ (glueImmersionOpen U m i).ι = m i :=
  IsOpenImmersion.lift_fac _ _ _

instance (i : κ) : IsClosedImmersion (glueImmersionLift hm i) := by
  have hle : glueImmersionOpen U m i ≤ (m i).coborderRange := inf_le_left
  have e : glueImmersionLift hm i ≫ X.homOfLE hle = (m i).liftCoborder := by
    rw [← cancel_mono (m i).coborderRange.ι, Category.assoc, Scheme.homOfLE_ι,
      glueImmersionLift_ι, Scheme.Hom.liftCoborder_ι]
  have : IsClosedImmersion (glueImmersionLift hm i ≫ X.homOfLE hle) := by
    rw [e]
    infer_instance
  exact IsClosedImmersion.of_comp _ (X.homOfLE hle)

variable (hcompat : ∀ (i j : κ) ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X),
    Set.range g ⊆ U j → (∃ h : T ⟶ Z i, h ≫ m i = g) → ∃ h : T ⟶ Z j, h ≫ m j = g)

include hcompat in
/-- **The kernels agree on overlaps** (one inequality): for a locally Noetherian `Y` with
`p : Y ⟶ O_i` and `q : Y ⟶ O_j` over `X`, the pullback of the kernel of the `j`-th closed
immersion along `q` is contained in the pullback of the kernel of the `i`-th along `p`. The closed
subscheme of `Y` cut out by the latter maps into `Z_i`, hence (being locally Noetherian, with image
in `U_j`) into `Z_j`, so the former vanishes on it. -/
theorem comap_ker_glueImmersionLift_le (i j : κ) {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (p : Y ⟶ (glueImmersionOpen U m i).toScheme) (q : Y ⟶ (glueImmersionOpen U m j).toScheme)
    (hpq : p ≫ (glueImmersionOpen U m i).ι = q ≫ (glueImmersionOpen U m j).ι) :
    (glueImmersionLift hm j).ker.comap q ≤ (glueImmersionLift hm i).ker.comap p := by
  set I := (glueImmersionLift hm i).ker.comap p
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  obtain ⟨a, ha⟩ := (exists_lift_iff_comap_ker_eq_bot (glueImmersionLift hm i)
    (I.subschemeι ≫ p)).mpr (by
      rw [IdealSheafData.comap_comp]
      exact IdealSheafData.comap_subschemeι_self I)
  have hrange : Set.range (I.subschemeι ≫ q ≫ (glueImmersionOpen U m j).ι) ⊆ U j := by
    rintro _ ⟨w, rfl⟩
    have hw : (I.subschemeι ≫ q ≫ (glueImmersionOpen U m j).ι) w ∈
        Set.range (glueImmersionOpen U m j).ι := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at hw
    exact (inf_le_right : glueImmersionOpen U m j ≤ U j) hw
  obtain ⟨b, hb⟩ := hcompat i j _ hrange ⟨a, by
    rw [← glueImmersionLift_ι hm i, reassoc_of% ha, hpq]⟩
  have hb' : b ≫ glueImmersionLift hm j = I.subschemeι ≫ q := by
    rw [← cancel_mono (glueImmersionOpen U m j).ι, Category.assoc, glueImmersionLift_ι, hb,
      Category.assoc]
  have h0 := (exists_lift_iff_comap_ker_eq_bot (glueImmersionLift hm j) _).mp ⟨b, hb'⟩
  rw [IdealSheafData.comap_comp] at h0
  have h1 : (glueImmersionLift hm j).ker.comap q ≤
      (⊥ : I.subscheme.IdealSheafData).map I.subschemeι :=
    (IdealSheafData.map_gc I.subschemeι _ ⊥).mp h0.le
  rwa [IdealSheafData.map_bot, IdealSheafData.ker_subschemeι] at h1

variable [IsLocallyNoetherian X]

/-- The pullback of `glueImmersionIncl U m i` and `glueImmersionIncl U m j` is locally
Noetherian. -/
instance (i j : κ) :
    IsLocallyNoetherian (pullback (glueImmersionIncl U m i) (glueImmersionIncl U m j)) :=
  isLocallyNoetherian_of_isOpenImmersion
    (pullback.fst (glueImmersionIncl U m i) (glueImmersionIncl U m j))

include hcompat in
/-- The kernels of the closed immersions `glueImmersionLift hm i` agree on the overlaps. -/
theorem comap_ker_glueImmersionLift_eq (i j : κ) :
    (glueImmersionLift hm i).ker.comap
        (pullback.fst (glueImmersionIncl U m i) (glueImmersionIncl U m j)) =
      (glueImmersionLift hm j).ker.comap
        (pullback.snd (glueImmersionIncl U m i) (glueImmersionIncl U m j)) := by
  have hpq : pullback.fst (glueImmersionIncl U m i) (glueImmersionIncl U m j) ≫
      (glueImmersionOpen U m i).ι =
        pullback.snd (glueImmersionIncl U m i) (glueImmersionIncl U m j) ≫
          (glueImmersionOpen U m j).ι := by
    rw [← glueImmersionIncl_ι U m i, ← glueImmersionIncl_ι U m j, pullback.condition_assoc]
  exact le_antisymm (comap_ker_glueImmersionLift_le hm hcompat j i _ _ hpq.symm)
    (comap_ker_glueImmersionLift_le hm hcompat i j _ _ hpq)

/-- The glued ideal sheaf on `glueImmersionUnion U m`. -/
def glueImmersionIdeal : (glueImmersionUnion U m).toScheme.IdealSheafData :=
  IdealSheafData.glue (glueImmersionIncl U m) (fun i => (glueImmersionLift hm i).ker)
    (exists_glueImmersionIncl_eq U m) (comap_ker_glueImmersionLift_eq hm hcompat)

theorem comap_glueImmersionIdeal (i : κ) :
    (glueImmersionIdeal hm hcompat).comap (glueImmersionIncl U m i) =
      (glueImmersionLift hm i).ker :=
  IdealSheafData.comap_glue _ _ i

/-- The glued immersion: the closed subscheme of `glueImmersionUnion U m` cut out by the glued
ideal sheaf, followed by the inclusion of the open `glueImmersionUnion U m` into `X`. -/
def glueImmersion : (glueImmersionIdeal hm hcompat).subscheme ⟶ X :=
  (glueImmersionIdeal hm hcompat).subschemeι ≫ (glueImmersionUnion U m).ι

instance : IsImmersion (glueImmersion hm hcompat) := by
  unfold glueImmersion
  infer_instance

/-- Every local immersion `m_i` factors through the glued immersion. -/
theorem exists_comp_glueImmersion_eq (i : κ) :
    ∃ d : Z i ⟶ (glueImmersionIdeal hm hcompat).subscheme, d ≫ glueImmersion hm hcompat = m i := by
  obtain ⟨d, hd⟩ := (IdealSheafData.exists_lift_subschemeι_iff (glueImmersionIdeal hm hcompat)
    (glueImmersionLift hm i ≫ glueImmersionIncl U m i)).mpr (by
      rw [IdealSheafData.comap_comp, comap_glueImmersionIdeal]
      exact (exists_lift_iff_comap_ker_eq_bot _ _).mp ⟨𝟙 _, Category.id_comp _⟩)
  refine ⟨d, ?_⟩
  rw [glueImmersion, reassoc_of% hd, glueImmersionIncl_ι, glueImmersionLift_ι]

/-- A morphism that factors through the glued immersion factors, near every point, through one
of the local immersions `m_i`, over the open `glueImmersionOpen U m i`. -/
theorem exists_lift_glueImmersionLift_of_exists_lift {T : Scheme.{u}} (g : T ⟶ X)
    (h : T ⟶ (glueImmersionIdeal hm hcompat).subscheme) (hg : h ≫ glueImmersion hm hcompat = g)
    (t : T) : ∃ i, g t ∈ glueImmersionOpen U m i ∧
      ∃ a : (g ⁻¹ᵁ glueImmersionOpen U m i).toScheme ⟶ Z i,
        a ≫ m i = (g ⁻¹ᵁ glueImmersionOpen U m i).ι ≫ g := by
  obtain ⟨i, y, hy⟩ := exists_glueImmersionIncl_eq U m ((glueImmersionIdeal hm hcompat).subschemeι
    (h t))
  have hgt : g t = (glueImmersionOpen U m i).ι y := by
    rw [← hg, glueImmersion, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hy,
      ← Scheme.Hom.comp_apply, glueImmersionIncl_ι]
  have hmem : g t ∈ glueImmersionOpen U m i := by
    rw [hgt, ← SetLike.mem_coe, ← Scheme.Opens.range_ι]
    exact ⟨y, rfl⟩
  refine ⟨i, hmem, ?_⟩
  let V := g ⁻¹ᵁ glueImmersionOpen U m i
  have hsub : Set.range (V.ι ≫ g) ⊆ Set.range (glueImmersionOpen U m i).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    exact v.2
  let k := IsOpenImmersion.lift (glueImmersionOpen U m i).ι (V.ι ≫ g) hsub
  have hk : k ≫ glueImmersionIncl U m i =
      V.ι ≫ h ≫ (glueImmersionIdeal hm hcompat).subschemeι := by
    rw [← cancel_mono (glueImmersionUnion U m).ι, Category.assoc, glueImmersionIncl_ι,
      IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, ← hg, glueImmersion]
  obtain ⟨a, ha⟩ := (exists_lift_iff_comap_ker_eq_bot (glueImmersionLift hm i) k).mpr (by
    rw [← comap_glueImmersionIdeal hm hcompat i, ← IdealSheafData.comap_comp, hk,
      IdealSheafData.comap_comp, IdealSheafData.comap_comp, IdealSheafData.comap_subschemeι_self,
      IdealSheafData.comap_bot, IdealSheafData.comap_bot])
  exact ⟨a, by rw [← glueImmersionLift_ι hm i, reassoc_of% ha, IsOpenImmersion.lift_fac]⟩

end Glue

/-- **A Zariski-local condition represented locally by immersions is represented by an
immersion.** Let `X` be locally Noetherian and `P` a condition on morphisms from locally Noetherian
schemes to `X`, stable under restriction to opens and local on the source. If every point of `X`
has an open neighbourhood `U` and an immersion `m : Z ⟶ X` with image in `U` such that a morphism
`g` with image in `U` satisfies `P` exactly when it factors through `m`, then some immersion
`Z ⟶ X` represents `P` on locally Noetherian schemes. -/
theorem exists_isImmersion_forall_exists_lift_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ X) → Prop)
    (hres : ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X) (V : T.Opens), P g →
      P (V.ι ≫ g))
    (hloc : ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X),
      (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ P (V.ι ≫ g)) → P g)
    (hrep : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (Z : Scheme.{u}) (m : Z ⟶ X) (_ : IsImmersion m),
      Set.range m ⊆ U ∧ ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X),
        Set.range g ⊆ U → (P g ↔ ∃ h : T ⟶ Z, h ≫ m = g)) :
    ∃ (Z : Scheme.{u}) (m : Z ⟶ X), IsImmersion m ∧
      ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X),
        (∃ h : T ⟶ Z, h ≫ m = g) ↔ P g := by
  choose U hxU Z m hm hmU hrepU using hrep
  have hcompat : ∀ (i j : X) ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ X),
      Set.range g ⊆ U j → (∃ h : T ⟶ Z i, h ≫ m i = g) → ∃ h : T ⟶ Z j, h ≫ m j = g := by
    intro i j T _ g hj hi
    have hgi : Set.range g ⊆ U i := by
      obtain ⟨h, rfl⟩ := hi
      exact (Set.range_comp_subset_range h (m i)).trans (hmU i)
    exact (hrepU j g hj).mp ((hrepU i g hgi).mpr hi)
  refine ⟨_, glueImmersion hmU hcompat, inferInstance, fun T _ g => ⟨?_, fun hP => ?_⟩⟩
  · rintro ⟨h, hg⟩
    refine hloc g fun t => ?_
    obtain ⟨i, hi, a, ha⟩ := exists_lift_glueImmersionLift_of_exists_lift hmU hcompat g h hg t
    have hrange : Set.range ((g ⁻¹ᵁ glueImmersionOpen U m i).ι ≫ g) ⊆ U i := by
      rintro _ ⟨v, rfl⟩
      exact (inf_le_right : glueImmersionOpen U m i ≤ U i) v.2
    exact ⟨g ⁻¹ᵁ glueImmersionOpen U m i, hi, (hrepU i _ hrange).mpr ⟨a, ha⟩⟩
  · refine exists_lift_of_mono_of_forall_exists _ g fun t => ?_
    have hrange : Set.range ((g ⁻¹ᵁ U (g t)).ι ≫ g) ⊆ U (g t) := by
      rintro _ ⟨v, rfl⟩
      exact v.2
    obtain ⟨h, hh⟩ := (hrepU (g t) _ hrange).mp (hres g _ hP)
    obtain ⟨d, hd⟩ := exists_comp_glueImmersion_eq hmU hcompat (g t)
    exact ⟨g ⁻¹ᵁ U (g t), hxU (g t), h ≫ d, by rw [Category.assoc, hd, hh]⟩

end AlgebraicGeometry.Scheme
