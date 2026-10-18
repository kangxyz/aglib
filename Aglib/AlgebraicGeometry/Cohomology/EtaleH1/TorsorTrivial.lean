/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorClass

/-!
# Trivial torsors have zero canonical Ext class

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Vanishing is proved from a genuine
global section by extending the augmentation-kernel difference map. The
converse uses precisely the retained Stacks03AJ bijectivity boundary.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u w
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X}
variable (P : Torsor L) (s : P.carrier.obj.obj (op (etaleTerminal X)))

/-- A chosen global section extends the difference map to the free presheaf. -/
def torsorBasedDifferencePresheaf : torsorFreePresheaf P ⟶ L.obj where
  app U := by
    let := P.sectionAction U
    exact AddCommGrpCat.ofHom (AddAction.TorsorAugmentation.basedDifference
      (P.unique_transport U) (P.restrictGlobalSection s U))
  naturality {U V} f := by
    let := P.sectionAction U
    let := P.sectionAction V
    ext x
    have h := AddAction.TorsorAugmentation.basedDifference_naturality
      (P.unique_transport U) (P.unique_transport V) (L.obj.map f).hom
      (P.carrier.obj.map f) (P.naturality f) (P.restrictGlobalSection s U)
    rw [P.restrictGlobalSection_naturality] at h
    exact DFunLike.congr_fun h x

/-- The section-based extension restricts to the canonical kernel difference. -/
theorem torsorBasedDifferencePresheaf_kernel :
    torsorKernelInclusion P ≫ torsorBasedDifferencePresheaf P s = torsorKernelDifference P := by
  ext U x
  let := P.sectionAction U
  exact (AddAction.TorsorAugmentation.kernelDifference_eq_based (P.unique_transport U)
    (P.restrictGlobalSection s U) x).symm

/-- The induced map from the actual free abelian sheaf. -/
def torsorBasedDifferenceSheaf : torsorFreeSheaf P ⟶ L :=
  ((sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).homEquiv
    (torsorFreePresheaf P) L).symm (torsorBasedDifferencePresheaf P s)

/-- The canonical kernel difference extends to the free sheaf when a section exists. -/
theorem torsorBasedDifferenceSheaf_kernel :
    torsorKernelSheafInclusion P ≫ torsorBasedDifferenceSheaf P s = torsorDifferenceSheafMap P := by
  let adj := sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  apply (adj.homEquiv (torsorKernelPresheaf P) L).injective
  change adj.homEquiv _ _
      ((presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
        (torsorKernelInclusion P) ≫ (adj.homEquiv _ _).symm (torsorBasedDifferencePresheaf P s)) =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorKernelDifference P))
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact torsorBasedDifferencePresheaf_kernel P s

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

include s in
/-- A genuine global torsor section forces the canonical Ext class to vanish. -/
theorem torsorExtClass_eq_zero_of_section : torsorExtClass P = 0 := by
  rw [torsorExtClass_eq, ← torsorBasedDifferenceSheaf_kernel P s,
    ← Abelian.Ext.mk₀_comp_mk₀]
  exact (torsorAugmentation_shortExact P).extClass_comp_assoc
    (Abelian.Ext.mk₀ (torsorBasedDifferenceSheaf P s))

@[simp] theorem torsorExtClass_trivial (L : AbelianSheaf.{u, u + 1} X) :
    torsorExtClass (trivialTorsor L) = 0 :=
  torsorExtClass_eq_zero_of_section (trivialTorsor L) 0

/-- Under the precise Stacks03AJ bijectivity premise, vanishing is equivalent
to an actual global torsor section. -/
theorem torsorExtClass_eq_zero_iff_globalSection (h : Stacks03AJ.{u, w} X) :
    torsorExtClass P = 0 ↔ Nonempty (P.carrier.obj.obj (op (etaleTerminal X))) := by
  constructor
  · intro hp
    have hc : torsorClassToH1 L (Quotient.mk (Torsor.isomorphicSetoid L) P) =
        torsorClassToH1 L (Quotient.mk (Torsor.isomorphicSetoid L) (trivialTorsor L)) :=
      hp.trans (torsorExtClass_trivial L).symm
    have he := (h.bijective L).injective hc
    obtain ⟨e⟩ := Quotient.exact he
    exact P.nonempty_globalSections_iff_trivial.mpr ⟨e.symm⟩
  · rintro ⟨t⟩
    exact torsorExtClass_eq_zero_of_section P t

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3ce59431d712a763cfb629793a2451535c269edb5852b31de63d3f48b45aafae.
Definitions, hypotheses and universes are retained modulo native names. -/
