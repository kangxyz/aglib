/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Gluing ideal sheaves along open covers

Let `f i : U i ⟶ X` be a jointly surjective family of open immersions and let `I i` be ideal sheaves
(Mathlib's `Scheme.IdealSheafData`) on the `U i` whose pullbacks to the overlaps agree,
`(I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j))`. This file
constructs the glued ideal sheaf `IdealSheafData.glue f I hf hI` on `X` and proves
`(glue f I hf hI).comap (f i) = I i` (`IdealSheafData.comap_glue`).

On an open `V` of `X`, the glued ideal `glueIdeal f I V` consists of the sections whose
restrictions to every affine open `W` of every `U i` with `W ≤ f i ⁻¹ᵁ V` lie in `I i`. The
proof uses:

* `mem_ideal_of_forall_exists`: membership in an ideal sheaf is local on affine opens;
* `ideal_le_comap_appLE_ideal_comap`, `ideal_comap_appLE_ideal_comap_le`: membership along an open
  immersion, read through `ideal_comap_of_isOpenImmersion`;
* `comap_appLE_le_comap_appLE`: the compatibility on the overlap `pullback (f i) (f j)` transfers
  membership from `I j` to `I i`;
* `mem_glueIdeal_of_forall_mem`: membership in `glueIdeal f I V` is tested on any family of affine
  opens `W k` of the `U (i k)` whose images cover `V`;
* `map_glueIdeal_basicOpen`: on affine opens the glued ideals localize, using a finite cover of the
  quasi-compact open `V` and the localization `Γ(X, X.basicOpen g)` of `Γ(X, V)` at `g`.

Mathlib's pushforward `IdealSheafData.map` is not used. The equation `(I.map j).comap j = I`, which
would let `⨅ i, (I i).map (f i)` serve as the gluing, holds for a quasi-compact open immersion `j`
(kernels of quasi-compact morphisms commute with open base change, Aglib's
`Scheme.Hom.ker_eq_comap_of_isPullback_of_isOpenImmersion`) but can fail otherwise (checked by hand,
not formalized here): for `X = Spec k[x, y₁, y₂, …]`, `j` the inclusion of
`D(x) ∪ ⋃ₙ D(yₙ)` and `I` the ideal of the disjoint union of the subschemes
`V(yₙ - 1, yₘ (m ≠ n), xⁿ) ⊆ D(yₙ)`, the ideal `(I.map j).ideal ⊤` is the kernel `a` of
`k[x, y₁, …] → ∏ₙ k[x]/(xⁿ)`, which contains no power of `x`, so `(I.map j).comap j` is not the
unit ideal on `D(x)`, whereas `I` is.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

section Local

variable {X Y : Scheme.{u}}

/-- Membership in an ideal sheaf is local: a section over an affine open `W` lies in `I.ideal W` if
every point of `W` has an affine open neighbourhood `W' ≤ W` on which its restriction lies in
`I.ideal W'`. -/
lemma mem_ideal_of_forall_exists (I : X.IdealSheafData) {W : X.affineOpens} {s : Γ(X, W)}
    (h : ∀ x ∈ W.1, ∃ (W' : X.affineOpens) (hle : W' ≤ W), x ∈ W'.1 ∧
      (X.presheaf.map (homOfLE hle).op).hom s ∈ I.ideal W') :
    s ∈ I.ideal W := by
  refine W.2.mem_ideal_iff.mpr fun x hx ↦ ?_
  obtain ⟨W', hle, hxW', hmem⟩ := h x hx
  have e : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ W'.1 x hxW' =
      X.presheaf.germ W.1 x hx :=
    X.presheaf.germ_res (homOfLE hle) x hxW'
  have h' := Ideal.mem_map_of_mem (X.presheaf.germ W'.1 x hxW').hom hmem
  rw [← I.map_ideal hle, Ideal.map_map, ← CommRingCat.hom_comp, e] at h'
  have e' : (X.presheaf.germ W'.1 x hxW').hom ((X.presheaf.map (homOfLE hle).op).hom s) =
      (X.presheaf.germ W.1 x hx).hom s := by
    rw [← e]
    rfl
  rw [e'] at h'
  exact h'

/-- The restriction along an endomorphism of an open in the opposite category is the identity on
ideals. -/
private lemma comap_presheaf_map_eq_self (X : Scheme.{u}) {W : X.Opens} (i : op W ⟶ op W)
    (K : Ideal Γ(X, W)) : K.comap (X.presheaf.map i).hom = K := by
  have : i = 𝟙 _ := rfl
  rw [this, X.presheaf.map_id, CommRingCat.hom_id, Ideal.comap_id]

/-- The restriction `g.appLE B A h` along an open immersion `g` maps `I.ideal B` into
`(I.comap g).ideal A`. -/
lemma ideal_le_comap_appLE_ideal_comap (I : X.IdealSheafData) (g : Y ⟶ X) [IsOpenImmersion g]
    (B : X.affineOpens) (A : Y.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ B.1) :
    I.ideal B ≤ ((I.comap g).ideal A).comap (g.appLE B A h).hom := by
  rw [ideal_comap_of_isOpenImmersion, Ideal.comap_comap, ← CommRingCat.hom_comp,
    Scheme.Hom.appLE_appIso_inv]
  exact I.ideal_le_comap_ideal (U := ⟨g ''ᵁ A.1, A.2.image_of_isOpenImmersion g⟩) (V := B) _

/-- Conversely, if `B` lies in the image `g ''ᵁ A`, a section over `B` whose restriction to `A`
lies in `(I.comap g).ideal A` lies in `I.ideal B`. -/
lemma ideal_comap_appLE_ideal_comap_le (I : X.IdealSheafData) (g : Y ⟶ X) [IsOpenImmersion g]
    (B : X.affineOpens) (A : Y.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ B.1) (hB : B.1 ≤ g ''ᵁ A.1) :
    ((I.comap g).ideal A).comap (g.appLE B A h).hom ≤ I.ideal B := by
  rw [ideal_comap_of_isOpenImmersion, Ideal.comap_comap, ← CommRingCat.hom_comp,
    Scheme.Hom.appLE_appIso_inv]
  refine (Ideal.comap_mono (I.ideal_le_comap_ideal (U := B)
    (V := ⟨g ''ᵁ A.1, A.2.image_of_isOpenImmersion g⟩) hB)).trans_eq ?_
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, ← Functor.map_comp]
  exact comap_presheaf_map_eq_self X _ _

/-- Restricting along `(g.appIso W).inv` and then along `g.appLE (g ''ᵁ W) W` is the identity on
ideals. -/
lemma comap_appIso_inv_comap_appLE (I : Y.IdealSheafData) (g : Y ⟶ X) [IsOpenImmersion g]
    (W : Y.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ (g ''ᵁ W.1)) :
    ((I.ideal W).comap (g.appLE (g ''ᵁ W.1) W h).hom).comap (g.appIso W.1).inv.hom =
      I.ideal W := by
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, Scheme.Hom.appIso_inv_appLE]
  exact comap_presheaf_map_eq_self Y _ _

/-- `appLE` along equal morphisms. -/
private lemma appLE_eq_of_eq {φ ψ : Y ⟶ X} (e : φ = ψ) (V : X.Opens) (A : Y.Opens) (h : A ≤ φ ⁻¹ᵁ V)
    (h' : A ≤ ψ ⁻¹ᵁ V) : φ.appLE V A h = ψ.appLE V A h' := by
  subst e
  rfl

/-- **Transfer along overlaps.** Let `f₁`, `f₂` be open immersions into `X` and let `I₁`, `I₂` be
ideal sheaves on their sources with equal pullbacks to `pullback f₁ f₂`. For affine opens `W₁`,
`W₂` over an open `V` of `X` with `f₁ ''ᵁ W₁ ⊆ f₂ ''ᵁ W₂`, a section over `V` whose restriction to
`W₂` lies in `I₂` restricts into `I₁` on `W₁`. -/
lemma comap_appLE_le_comap_appLE {U₁ U₂ : Scheme.{u}} (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] {I₁ : U₁.IdealSheafData} {I₂ : U₂.IdealSheafData}
    (hI : I₁.comap (pullback.fst f₁ f₂) = I₂.comap (pullback.snd f₁ f₂)) {V : X.Opens}
    (W₁ : U₁.affineOpens) (W₂ : U₂.affineOpens) (h₁ : W₁.1 ≤ f₁ ⁻¹ᵁ V) (h₂ : W₂.1 ≤ f₂ ⁻¹ᵁ V)
    (hW : W₁.1 ≤ f₁ ⁻¹ᵁ (f₂ ''ᵁ W₂.1)) :
    (I₂.ideal W₂).comap (f₂.appLE V W₂ h₂).hom ≤ (I₁.ideal W₁).comap (f₁.appLE V W₁ h₁).hom := by
  have hrange : W₁.1 ≤ (pullback.fst f₁ f₂).opensRange := by
    intro w hw
    obtain ⟨w₂, -, hw₂⟩ : f₁ w ∈ f₂ '' (W₂.1 : Set U₂) := hW hw
    have hw' : w ∈ Set.range (pullback.fst f₁ f₂) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨w₂, hw₂⟩
    exact Scheme.Hom.mem_opensRange.mpr hw'
  let A : (pullback f₁ f₂).affineOpens :=
    ⟨pullback.fst f₁ f₂ ⁻¹ᵁ W₁.1, W₁.2.preimage_of_isOpenImmersion _ hrange⟩
  have hA₁ : A.1 ≤ pullback.fst f₁ f₂ ⁻¹ᵁ W₁.1 := le_rfl
  have hA₂ : A.1 ≤ pullback.snd f₁ f₂ ⁻¹ᵁ W₂.1 := by
    intro p hp
    obtain ⟨w₂, hw₂, hw₂'⟩ : f₁ (pullback.fst f₁ f₂ p) ∈ f₂ '' (W₂.1 : Set U₂) :=
      hW (show pullback.fst f₁ f₂ p ∈ W₁.1 from hp)
    have hc : f₂ (pullback.snd f₁ f₂ p) = f₁ (pullback.fst f₁ f₂ p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have hinj : w₂ = pullback.snd f₁ f₂ p := f₂.isOpenEmbedding.injective (hw₂'.trans hc.symm)
    change pullback.snd f₁ f₂ p ∈ W₂.1
    rw [← hinj]
    exact hw₂
  have hB : W₁.1 ≤ pullback.fst f₁ f₂ ''ᵁ (pullback.fst f₁ f₂ ⁻¹ᵁ W₁.1) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact le_inf hrange le_rfl
  have key : f₂.appLE V W₂ h₂ ≫ (pullback.snd f₁ f₂).appLE W₂ A hA₂ =
      f₁.appLE V W₁ h₁ ≫ (pullback.fst f₁ f₂).appLE W₁ A hA₁ := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq pullback.condition.symm _ _ _ _
  calc (I₂.ideal W₂).comap (f₂.appLE V W₂ h₂).hom
      ≤ (((I₂.comap (pullback.snd f₁ f₂)).ideal A).comap
          ((pullback.snd f₁ f₂).appLE W₂ A hA₂).hom).comap (f₂.appLE V W₂ h₂).hom :=
        Ideal.comap_mono (ideal_le_comap_appLE_ideal_comap I₂ _ W₂ A hA₂)
    _ = ((I₁.comap (pullback.fst f₁ f₂)).ideal A).comap
          (f₁.appLE V W₁ h₁ ≫ (pullback.fst f₁ f₂).appLE W₁ A hA₁).hom := by
        rw [Ideal.comap_comap, ← CommRingCat.hom_comp, key, hI]
    _ = (((I₁.comap (pullback.fst f₁ f₂)).ideal A).comap
          ((pullback.fst f₁ f₂).appLE W₁ A hA₁).hom).comap (f₁.appLE V W₁ h₁).hom := by
        rw [Ideal.comap_comap, CommRingCat.hom_comp]
    _ ≤ (I₁.ideal W₁).comap (f₁.appLE V W₁ h₁).hom :=
        Ideal.comap_mono (ideal_comap_appLE_ideal_comap_le I₁ _ W₁ A hA₁ hB)

/-- If the restriction of `b` to the basic open of `c` in an affine open `W` lies in `I`, then
`c ^ n * b` lies in `I.ideal W` for some `n`. -/
lemma exists_pow_mul_mem_of_map_mem (I : X.IdealSheafData) (W : X.affineOpens) (c b : Γ(X, W))
    (h : (X.presheaf.map (homOfLE (X.basicOpen_le c)).op).hom b ∈
      I.ideal (X.affineBasicOpen c)) :
    ∃ n : ℕ, c ^ n * b ∈ I.ideal W := by
  have := W.2.isLocalization_basicOpen c
  rw [← I.map_ideal_basicOpen] at h
  obtain ⟨m, hm, hmb⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers c) Γ(X, X.basicOpen c) (I.ideal W) b).mp h
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm
  exact ⟨n, hmb⟩

end Local

section Glue

variable {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}

/-- The ideal of sections of `X` over `V` whose restrictions to all affine opens `W` of all `U i`
with `W ≤ f i ⁻¹ᵁ V` lie in `I i`. On affine opens these are the ideals of the glued ideal sheaf
`IdealSheafData.glue`. -/
def glueIdeal (f : ∀ i, U i ⟶ X) (I : ∀ i, (U i).IdealSheafData) (V : X.Opens) :
    Ideal Γ(X, V) :=
  ⨅ (i : ι) (W : (U i).affineOpens) (h : W.1 ≤ f i ⁻¹ᵁ V),
    ((I i).ideal W).comap ((f i).appLE V W h).hom

variable {f : ∀ i, U i ⟶ X} {I : ∀ i, (U i).IdealSheafData}

lemma mem_glueIdeal {V : X.Opens} {s : Γ(X, V)} :
    s ∈ glueIdeal f I V ↔ ∀ i (W : (U i).affineOpens) (h : W.1 ≤ f i ⁻¹ᵁ V),
      ((f i).appLE V W h).hom s ∈ (I i).ideal W := by
  simp only [glueIdeal, Ideal.mem_iInf, Ideal.mem_comap]

variable [∀ i, IsOpenImmersion (f i)]

/-- Membership in `glueIdeal f I V` can be tested on any family of affine opens `W k` of the
`U (i k)` over `V` whose images cover `V`. -/
lemma mem_glueIdeal_of_forall_mem
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j)))
    {V : X.Opens} {κ : Type*} (i : κ → ι) (W : ∀ k, (U (i k)).affineOpens)
    (hW : ∀ k, (W k).1 ≤ f (i k) ⁻¹ᵁ V) (hV : ∀ x ∈ V, ∃ k, x ∈ f (i k) ''ᵁ (W k).1)
    {s : Γ(X, V)} (hs : ∀ k, ((f (i k)).appLE V (W k) (hW k)).hom s ∈ (I (i k)).ideal (W k)) :
    s ∈ glueIdeal f I V := by
  rw [mem_glueIdeal]
  intro j W' hW'
  refine (I j).mem_ideal_of_forall_exists fun w hw ↦ ?_
  obtain ⟨k, hk⟩ := hV (f j w) (hW' hw)
  obtain ⟨W'', hW''aff, hwW'', hW''le⟩ := Opens.isBasis_iff_nbhd.mp (U j).isBasis_affineOpens
    (show w ∈ W'.1 ⊓ f j ⁻¹ᵁ (f (i k) ''ᵁ (W k).1) from ⟨hw, hk⟩)
  refine ⟨⟨W'', hW''aff⟩, hW''le.trans inf_le_left, hwW'', ?_⟩
  have hmem := comap_appLE_le_comap_appLE (f j) (f (i k)) (hI j (i k)) ⟨W'', hW''aff⟩ (W k)
    ((hW''le.trans inf_le_left).trans hW') (hW k) (hW''le.trans inf_le_right) (hs k)
  rw [Ideal.mem_comap] at hmem
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  exact hmem

/-- If the restriction of `a` to the basic open of `g` in an affine open `V` lies in the glued
ideal, then so does `g ^ n * a` for some `n`. -/
lemma exists_pow_mul_mem_glueIdeal (hf : ∀ x : X, ∃ i y, f i y = x)
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j)))
    (V : X.affineOpens) (g a : Γ(X, V))
    (ha : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom a ∈
      glueIdeal f I (X.basicOpen g)) :
    ∃ n : ℕ, g ^ n * a ∈ glueIdeal f I V := by
  classical
  have hloc : ∀ x : V.1, ∃ (i : ι) (W : (U i).affineOpens) (_ : W.1 ≤ f i ⁻¹ᵁ V.1),
      x.1 ∈ f i ''ᵁ W.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨W, hWaff, hyW, hWle⟩ := Opens.isBasis_iff_nbhd.mp (U i).isBasis_affineOpens
      (show y ∈ f i ⁻¹ᵁ V.1 from hx)
    exact ⟨i, ⟨W, hWaff⟩, hWle, ⟨y, hyW, rfl⟩⟩
  choose i W hW hxW using hloc
  have hpow : ∀ x : V.1, ∃ n : ℕ,
      ((f (i x)).appLE V (W x) (hW x)).hom (g ^ n * a) ∈ (I (i x)).ideal (W x) := by
    intro x
    have hD : ((U (i x)).affineBasicOpen (((f (i x)).appLE V (W x) (hW x)).hom g)).1 ≤
        f (i x) ⁻¹ᵁ X.basicOpen g :=
      (Scheme.basicOpen_appLE (f (i x)) (W x).1 V.1 (hW x) g).trans_le inf_le_right
    have h' : ((U (i x)).presheaf.map (homOfLE ((U (i x)).basicOpen_le
        (((f (i x)).appLE V (W x) (hW x)).hom g))).op).hom
          (((f (i x)).appLE V (W x) (hW x)).hom a) ∈
        (I (i x)).ideal ((U (i x)).affineBasicOpen (((f (i x)).appLE V (W x) (hW x)).hom g)) := by
      have hmem := (mem_glueIdeal.mp ha) (i x) _ hD
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at hmem
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
      exact hmem
    obtain ⟨n, hn⟩ := (I (i x)).exists_pow_mul_mem_of_map_mem (W x) _ _ h'
    exact ⟨n, by rwa [map_mul, map_pow]⟩
  choose n hn using hpow
  obtain ⟨t, ht⟩ := V.2.isCompact.elim_finite_subcover
    (fun x : V.1 ↦ ((f (i x) ''ᵁ (W x).1 : X.Opens) : Set X))
    (fun x ↦ (f (i x) ''ᵁ (W x).1).isOpen) (fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  refine ⟨∑ x ∈ t, n x, mem_glueIdeal_of_forall_mem hI (κ := t) (fun x ↦ i x.1)
    (fun x ↦ W x.1) (fun x ↦ hW x.1) ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact ⟨⟨x, hxt⟩, hyx⟩
  · rintro ⟨x, hxt⟩
    dsimp only
    rw [← Finset.add_sum_erase t n hxt, pow_add, mul_comm (g ^ n x), mul_assoc, map_mul]
    exact Ideal.mul_mem_left _ _ (hn x)

/-- On affine opens, the glued ideals satisfy the basic-open condition of an ideal sheaf. -/
lemma map_glueIdeal_basicOpen (hf : ∀ x : X, ∃ i y, f i y = x)
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j)))
    (V : X.affineOpens) (g : Γ(X, V)) :
    (glueIdeal f I V).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom =
      glueIdeal f I (X.basicOpen g) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, mem_glueIdeal]
    intro i W h
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
    exact mem_glueIdeal.mp hs i W _
  · intro t ht
    have := V.2.isLocalization_basicOpen g
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers g) t
    have ha : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom a ∈
        glueIdeal f I (X.basicOpen g) := by
      have hmul := Ideal.mul_mem_right (algebraMap Γ(X, V) Γ(X, X.basicOpen g) s.1) _ ht
      rwa [IsLocalization.mk'_spec] at hmul
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_glueIdeal hf hI V g a ha
    exact (IsLocalization.mk'_mem_map_algebraMap_iff (Submonoid.powers g) Γ(X, X.basicOpen g)
      _ a s).mpr ⟨g ^ n, pow_mem (Submonoid.mem_powers g) n, hn⟩

variable (f I) in
/-- The ideal sheaf on `X` glued from ideal sheaves `I i` on the members `f i : U i ⟶ X` of an
open cover that agree on the overlaps. -/
def glue (hf : ∀ x : X, ∃ i y, f i y = x)
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j))) :
    X.IdealSheafData where
  ideal V := glueIdeal f I V
  map_ideal_basicOpen V g := map_glueIdeal_basicOpen hf hI V g

lemma glue_ideal (hf : ∀ x : X, ∃ i y, f i y = x)
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j)))
    (V : X.affineOpens) : (glue f I hf hI).ideal V = glueIdeal f I V :=
  rfl

/-- **Gluing of ideal sheaves.** The glued ideal sheaf pulls back to `I i` along each `f i`. -/
theorem comap_glue (hf : ∀ x : X, ∃ i y, f i y = x)
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j)))
    (i : ι) : (glue f I hf hI).comap (f i) = I i := by
  refine IdealSheafData.ext (funext fun W ↦ ?_)
  rw [ideal_comap_of_isOpenImmersion, glue_ideal]
  have hle : W.1 ≤ f i ⁻¹ᵁ (f i ''ᵁ W.1) := (Scheme.Hom.preimage_image_eq (f i) W.1).ge
  have h₁ : glueIdeal f I (f i ''ᵁ W.1) ≤
      ((I i).ideal W).comap ((f i).appLE (f i ''ᵁ W.1) W hle).hom :=
    iInf_le_of_le i (iInf_le_of_le W (iInf_le _ hle))
  have h₂ : ((I i).ideal W).comap ((f i).appLE (f i ''ᵁ W.1) W hle).hom ≤
      glueIdeal f I (f i ''ᵁ W.1) :=
    le_iInf fun j ↦ le_iInf fun W' ↦ le_iInf fun h' ↦
      comap_appLE_le_comap_appLE (f j) (f i) (hI j i) W' W h' hle h'
  have e := comap_appIso_inv_comap_appLE (I i) (f i) W hle
  exact le_antisymm ((Ideal.comap_mono h₁).trans_eq e) (e.symm.trans_le (Ideal.comap_mono h₂))

/-- Ideal sheaves on the members of an open cover that agree on the overlaps come from an ideal
sheaf on `X`. -/
theorem exists_comap_eq_of_isOpenImmersion (hf : ∀ x : X, ∃ i y, f i y = x)
    (hI : ∀ i j, (I i).comap (pullback.fst (f i) (f j)) = (I j).comap (pullback.snd (f i) (f j))) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (f i) = I i :=
  ⟨glue f I hf hI, comap_glue hf hI⟩

end Glue

end AlgebraicGeometry.Scheme.IdealSheafData
