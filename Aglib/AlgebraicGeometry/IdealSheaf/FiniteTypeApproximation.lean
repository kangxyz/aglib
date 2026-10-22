/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.FiniteTypeExtension
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Directed finite-type subideals with prescribed supremum

Every native ideal on a qcqs scheme is the supremum of its finite-type subideals.
The local element approximation uses exact ambient-bounded extension of a principal
ideal from an affine open. Nilpotents and arbitrary coefficient rings are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Restriction to an affine open, on global sections, is the original ring-isomorphism
transport of the native ideal. -/
theorem ideal_comap_opens_top (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap U.val.ι).ideal ⟨⊤, by
      let : IsAffine U.val.toScheme := U.property
      exact isAffineOpen_top _⟩ =
      (I.ideal U).map U.val.topIso.inv.hom := by
  let : IsAffine U.val.toScheme := U.property
  rw [ideal_comap_eq_map_appLE_of_isOpenImmersion I U.val.ι U
    ⟨⊤, isAffineOpen_top _⟩ U.val.ι_preimage_self.ge U.val.ι_image_top.ge]
  congr 1
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

/-- A globally generated ideal with finitely many generators is finite type on every
scheme, not just on affine schemes. -/
theorem affineLocallyFG_ofIdealTop (A : Ideal Γ(X, ⊤)) (hA : A.FG) :
    (ofIdealTop A).AffineLocallyFG := by
  intro U
  rw [ofIdealTop_ideal]
  exact hA.map _

/-- Finite type is closed under the native sum of ideal sheaves. -/
theorem AffineLocallyFG.sup {I J : X.IdealSheafData}
    (hI : I.AffineLocallyFG) (hJ : J.AffineLocallyFG) : (I ⊔ J).AffineLocallyFG := by
  intro U
  exact Submodule.FG.sup (hI U) (hJ U)

/-- The zero ideal is of finite type on any scheme. -/
theorem affineLocallyFG_bot : (⊥ : X.IdealSheafData).AffineLocallyFG :=
  fun _ => Submodule.fg_bot

/-- Every affine section of an ideal lies in a finite-type subideal on the whole
qcqs scheme. The chosen subideal stays inside the original ideal. -/
theorem exists_affineLocallyFG_le_of_mem
    [CompactSpace X] [QuasiSeparatedSpace X] (I : X.IdealSheafData)
    (U : X.affineOpens) (s : Γ(X, U)) (hs : s ∈ I.ideal U) :
    ∃ J : X.IdealSheafData, J ≤ I ∧ J.AffineLocallyFG ∧ s ∈ J.ideal U := by
  let : IsAffine U.val.toScheme := U.property
  let a := U.val.topIso.inv s
  let K : U.val.toScheme.IdealSheafData := ofIdealTop (Ideal.span {a})
  have hK : K.AffineLocallyFG := affineLocallyFG_ofIdealTop _ (Submodule.fg_span_singleton a)
  have hKtop : K.ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {a} :=
    (equivOfIsAffine (X := U.val.toScheme)).apply_symm_apply (Ideal.span {a})
  have hKI : K ≤ I.comap U.val.ι := by
    apply le_of_isAffine
    rw [hKtop, ideal_comap_opens_top]
    exact Ideal.span_le.mpr (by
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact Ideal.mem_map_of_mem U.val.topIso.inv.hom hs)
  obtain ⟨J, hJI, hJ, hJU⟩ :=
    exists_affineLocallyFG_extension_le U.val U.property.isCompact I K hK hKI
  refine ⟨J, hJI, hJ, ?_⟩
  have ha : a ∈ (J.ideal U).map U.val.topIso.inv.hom := by
    rw [← ideal_comap_opens_top, hJU, hKtop]
    exact Ideal.subset_span (Set.mem_singleton a)
  have hmap : ((J.ideal U).map U.val.topIso.inv.hom).comap U.val.topIso.inv.hom =
      J.ideal U :=
    Ideal.comap_map_of_bijective U.val.topIso.inv.hom
      (ConcreteCategory.bijective_of_isIso U.val.topIso.inv)
  change s ∈ ((J.ideal U).map U.val.topIso.inv.hom).comap U.val.topIso.inv.hom at ha
  rwa [hmap] at ha

/-- The actual finite-type native subideals of a fixed ambient ideal. -/
def FiniteTypeSubideal (I : X.IdealSheafData) :=
  {J : X.IdealSheafData // J ≤ I ∧ J.AffineLocallyFG}

instance (I : X.IdealSheafData) : PartialOrder (FiniteTypeSubideal I) :=
  inferInstanceAs (PartialOrder {J : X.IdealSheafData // J ≤ I ∧ J.AffineLocallyFG})

instance (I : X.IdealSheafData) : Nonempty (FiniteTypeSubideal I) :=
  ⟨⟨⊥, bot_le, affineLocallyFG_bot⟩⟩

instance (I : X.IdealSheafData) : IsDirectedOrder (FiniteTypeSubideal I) where
  directed J K := ⟨⟨J.val ⊔ K.val, sup_le J.property.1 K.property.1,
    J.property.2.sup K.property.2⟩,
    (show J.val ≤ J.val ⊔ K.val from le_sup_left),
    (show K.val ≤ J.val ⊔ K.val from le_sup_right)⟩

/-- The index of actual finite-type subideals is a nonempty filtered category. -/
instance (I : X.IdealSheafData) : IsFiltered (FiniteTypeSubideal I) :=
  CategoryTheory.isFiltered_of_directed_le_nonempty _

/-- Every native ideal on a qcqs scheme is exactly the supremum of its actual
finite-type subideals. -/
theorem iSup_finiteTypeSubideal [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) : (⨆ J : FiniteTypeSubideal I, J.val) = I := by
  apply le_antisymm
  · exact iSup_le fun J => J.property.1
  · intro U s hs
    obtain ⟨J, hJI, hJ, hsJ⟩ := exists_affineLocallyFG_le_of_mem I U s hs
    exact (ideal_mono (le_iSup (fun J : FiniteTypeSubideal I => J.val)
      ⟨J, hJI, hJ⟩) U) hsJ

end AlgebraicGeometry.Scheme.IdealSheafData
