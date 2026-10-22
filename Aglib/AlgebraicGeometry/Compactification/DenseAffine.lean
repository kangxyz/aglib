/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.AffineOpen
public import Aglib.AlgebraicGeometry.Compactification.FiniteDisjointOpens
public import Aglib.AlgebraicGeometry.Properties.DenseAffine

/-!
# Dense affine opens with actual compactifications

Choose affine source pieces inside inverse images of affine base charts.
The subordinate disjoint enlargement contains every generic point; its
compactification is obtained by finite disjoint union of the actual affine
piece compactifications. This gives a finite dense cover, including the
empty-source case, with a dense common intersection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An affine source open lying over an affine base open has an actual
schematically dense compactification over the entire base. -/
theorem exists_schematicallyDense_compactification_of_affineOpen_le_preimage
    {X S : Scheme.{u}} [NoetherianSpace X] (p : X ⟶ S) [LocallyOfFiniteType p]
    (U : X.Opens) (O : S.Opens) (hU : IsAffineOpen U) (hO : IsAffineOpen O)
    (hUO : U ≤ p ⁻¹ᵁ O) :
    ∃ C : Compactification (U.ι ≫ p), IsSchemeTheoreticallyDominant C.j := by
  let : NoetherianSpace U.toScheme := by
    change NoetherianSpace (U : Set X)
    infer_instance
  let : IsAffine U.toScheme := hU
  let : IsAffine O.toScheme := hO
  let k := O.toScheme.isoSpec.inv ≫ O.ι
  let f := p.resLE O U hUO ≫ O.toScheme.isoSpec.hom
  have hfac : f ≫ k = U.ι ≫ p := by
    simp only [f, k, Category.assoc, Iso.hom_inv_id_assoc, resLE_comp_ι]
  have hk : IsOpenImmersion k := by dsimp only [k]; infer_instance
  have hf : LocallyOfFiniteType f := by dsimp only [f]; infer_instance
  have hq : QuasiCompact (f ≫ k) := inferInstance
  have H := @exists_schematicallyDense_compactification_through_affineOpen
    U.toScheme S inferInstance Γ(O.toScheme, ⊤) inferInstance k hk f hf hq
  have transport (a b : U.toScheme ⟶ S) (h : a = b) :
      (∃ C : Compactification a, IsSchemeTheoreticallyDominant C.j) →
        (∃ C : Compactification b, IsSchemeTheoreticallyDominant C.j) := by
    subst b
    exact id
  exact transport _ _ hfac H

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- Every point has a dense affine neighborhood whose original structural
map has a schematically dense compactification over the arbitrary base. -/
theorem exists_dense_affineOpen_compactification_mem
    {X S : Scheme.{u}} [NoetherianSpace X] (p : X ⟶ S) [LocallyOfFiniteType p]
    (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ genericPoints X ⊆ U ∧
      Dense (U : Set X) ∧
      ∃ C : Hom.Compactification (U.ι ≫ p), IsSchemeTheoreticallyDominant C.j := by
  classical
  obtain ⟨O₀, hO₀, hxO₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (show p x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVO⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ p ⁻¹ᵁ O₀ from hxO₀)
  have hchart (z : genericPoints X) : ∃ O : S.Opens, IsAffineOpen O ∧ p z.val ∈ O := by
    obtain ⟨O, hO, hzO, -⟩ := exists_isAffineOpen_mem_and_subset
      (show p z.val ∈ (⊤ : S.Opens) from trivial)
    exact ⟨O, hO, hzO⟩
  choose O hO hzO using hchart
  obtain ⟨A, hA, W, z, hW, hWN, hdisj, hVdisj, hgen⟩ :=
    exists_finite_disjoint_affine_enlargement NoetherianSpace.finite_irreducibleComponents
      V (fun z => p ⁻¹ᵁ O z) hzO
  let : Fintype A := hA
  obtain ⟨C, -⟩ := p.exists_schematicallyDense_compactification_of_affineOpen_le_preimage
    V O₀ hV hO₀ hVO
  have hCW (a : A) : ∃ C : Hom.Compactification ((W a).ι ≫ p),
      IsSchemeTheoreticallyDominant C.j :=
    p.exists_schematicallyDense_compactification_of_affineOpen_le_preimage
      (W a) (O (z a)) (hW a) (hO (z a)) (hWN a)
  let CW (a : A) := (hCW a).choose
  obtain ⟨D, hD⟩ := Hom.exists_schematicallyDense_compactification_sup_iSup
    p V W hdisj hVdisj C CW
  refine ⟨V ⊔ ⨆ a, W a,
    hV.sup_of_disjoint (IsAffineOpen.iSup_of_disjoint hW hdisj) hVdisj,
    (show V ≤ V ⊔ ⨆ a, W a from le_sup_left) hxV, hgen, ?_, D, hD⟩
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro y
  exact closure_mono hgen (by rw [genericPoints.closure]; trivial)

/-- A finite dense affine cover with dense common intersection and actual
schematically dense compactifications of every original chart map. The
finite index may be empty when the source is empty. -/
theorem exists_finite_dense_affine_compactifiable_cover
    {X S : Scheme.{u}} [NoetherianSpace X] (p : X ⟶ S) [LocallyOfFiniteType p] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i) ∧ Dense (U i : Set X) ∧ genericPoints X ⊆ U i ∧
        ∃ C : Hom.Compactification ((U i).ι ≫ p), IsSchemeTheoreticallyDominant C.j) ∧
      (⨆ i, U i) = ⊤ ∧ Dense ((⨅ i, U i : X.Opens) : Set X) := by
  classical
  choose U hUaff hUmem hUgen hUdense hC using exists_dense_affineOpen_compactification_mem p
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, (U x : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hUmem x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen) hcover
  refine ⟨s, inferInstance, fun x => U x.val,
    fun x => ⟨hUaff x.val, hUdense x.val, hUgen x.val, hC x.val⟩, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  · apply Dense.mono ?_ (dense_iff_closure_eq.mpr (genericPoints.closure (α := X)))
    intro x hx
    change x ∈ (((⨅ a : s, U a.val) : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun a => hUgen a.val hx

end AlgebraicGeometry.Scheme
