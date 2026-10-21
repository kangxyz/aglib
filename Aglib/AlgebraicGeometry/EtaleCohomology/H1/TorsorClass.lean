/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorCohomology

/-!
# Naturality and isomorphism-class descent of the canonical torsor Ext class

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. All maps below act on genuine
sheaf torsors and their constructed augmentation extensions.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}} {L M : AbelianSheaf.{u, u + 1} X}

/-- A torsor morphism relative to an actual coefficient sheaf morphism. -/
structure Torsor.Hom (q : L ⟶ M) (P : Torsor L) (Q : Torsor M) where
  /-- The morphism of carrier sheaves underlying the coefficient-relative torsor morphism. -/
  map : P.carrier ⟶ Q.carrier
  equivariant : ∀ U a t,
    map.hom.app U (P.action U a t) = Q.action U (q.hom.app U a) (map.hom.app U t)

variable {q : L ⟶ M} {P : Torsor L} {Q : Torsor M}

/-- The free-abelian presheaf morphism induced by a torsor morphism. -/
def torsorFreePresheafMap (r : Torsor.Hom q P Q) : torsorFreePresheaf P ⟶ torsorFreePresheaf Q :=
  Functor.whiskerRight r.map.hom AddCommGrpCat.free

/-- Torsor morphisms commute with the actual augmentation. -/
theorem torsorFreePresheafMap_augmentation (r : Torsor.Hom q P Q) :
    torsorFreePresheafMap r ≫ torsorAugmentationPresheaf Q = torsorAugmentationPresheaf P := by
  ext U x
  change FreeAbelianGroup.lift (fun _ => (1 : ULift.{u + 1} ℤ))
      (FreeAbelianGroup.map (r.map.hom.app U) x) =
    FreeAbelianGroup.lift (fun _ => (1 : ULift.{u + 1} ℤ)) x
  exact (FreeAbelianGroup.lift_comp _ (fun _ => (1 : ULift.{u + 1} ℤ)) x).symm

/-- The induced map on actual augmentation kernels is the universal kernel lift. -/
def torsorKernelPresheafMap (r : Torsor.Hom q P Q) :
    torsorKernelPresheaf P ⟶ torsorKernelPresheaf Q :=
  (KernelFork.IsLimit.lift' (torsorKernelIsLimit Q) (torsorKernelInclusion P ≫
    torsorFreePresheafMap r)
    (by rw [Category.assoc, torsorFreePresheafMap_augmentation,
      torsorKernelInclusion_augmentation])).1

@[reassoc] theorem torsorKernelPresheafMap_inclusion (r : Torsor.Hom q P Q) :
    torsorKernelPresheafMap r ≫ torsorKernelInclusion Q =
      torsorKernelInclusion P ≫ torsorFreePresheafMap r :=
  (KernelFork.IsLimit.lift' (torsorKernelIsLimit Q) (torsorKernelInclusion P ≫
    torsorFreePresheafMap r)
    (by rw [Category.assoc, torsorFreePresheafMap_augmentation,
      torsorKernelInclusion_augmentation])).2

/-- Explicit restriction/coefficient formula for the universal kernel map. -/
theorem torsorKernelPresheafMap_apply (r : Torsor.Hom q P Q) (U : X.Etaleᵒᵖ)
    (x : AddAction.TorsorAugmentation.AugmentationKernel (P.carrier.obj.obj U)) :
    (torsorKernelPresheafMap r).app U x =
      AddAction.TorsorAugmentation.kernelMap (r.map.hom.app U) x := by
  apply Subtype.ext
  exact congrArg (fun k : torsorKernelPresheaf P ⟶ torsorFreePresheaf Q => k.app U x)
    (torsorKernelPresheafMap_inclusion r)

/-- Naturality of the canonical torsor-difference morphism before sheafification. -/
theorem torsorKernelDifference_naturality (r : Torsor.Hom q P Q) :
    torsorKernelPresheafMap r ≫ torsorKernelDifference Q =
      torsorKernelDifference P ≫ q.hom := by
  ext U x
  let := P.sectionAction U
  let := Q.sectionAction U
  change AddAction.TorsorAugmentation.kernelDifference (Q.unique_transport U)
      ((torsorKernelPresheafMap r).app U x) =
    q.hom.app U (AddAction.TorsorAugmentation.kernelDifference (P.unique_transport U) x)
  rw [torsorKernelPresheafMap_apply]
  exact AddAction.TorsorAugmentation.kernelDifference_naturality (P.unique_transport U)
    (Q.unique_transport U) (q.hom.app U).hom (r.map.hom.app U) (r.equivariant U) x

/-- The map on sheafified augmentation kernels. -/
def torsorKernelSheafMap (r : Torsor.Hom q P Q) : torsorKernelSheaf P ⟶ torsorKernelSheaf Q :=
  (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
    (torsorKernelPresheafMap r)

/-- The map on free abelian sheaves obtained by sheafifying the map induced by the torsor
morphism. -/
def torsorFreeSheafMap (r : Torsor.Hom q P Q) : torsorFreeSheaf P ⟶ torsorFreeSheaf Q :=
  (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
    (torsorFreePresheafMap r)

/-- Morphism of the actual augmentation short exact sequences. -/
def torsorAugmentationComplexMap (r : Torsor.Hom q P Q) :
    torsorAugmentationComplex P ⟶ torsorAugmentationComplex Q where
  τ₁ := torsorKernelSheafMap r
  τ₂ := torsorFreeSheafMap r
  τ₃ := 𝟙 _
  comm₁₂ := by
    change (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map _ ≫
      (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map _ = _
    rw [← Functor.map_comp, torsorKernelPresheafMap_inclusion, Functor.map_comp]
    rfl
  comm₂₃ := by
    change (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map _ ≫
      (presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map _ = _
    rw [← Functor.map_comp, torsorFreePresheafMap_augmentation]
    exact (Category.comp_id _).symm

/-- The canonical difference map commutes with sheafification and coefficient maps. -/
theorem torsorDifferenceSheafMap_naturality (r : Torsor.Hom q P Q) :
    torsorKernelSheafMap r ≫ torsorDifferenceSheafMap Q = torsorDifferenceSheafMap P ≫ q := by
  let adj := sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  apply (adj.homEquiv (torsorKernelPresheaf P) M).injective
  change adj.homEquiv _ _
      ((presheafToSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).map
        (torsorKernelPresheafMap r) ≫ (adj.homEquiv _ _).symm (torsorKernelDifference Q)) =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm (torsorKernelDifference P) ≫ q)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact torsorKernelDifference_naturality r

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Naturality of the constructed torsor class for every actual equivariant
sheaf map with the specified coefficient map. -/
theorem torsorExtClass_naturality (r : Torsor.Hom q P Q) :
    coefficientMap q (torsorExtClass P) = torsorExtClass Q := by
  have h := ShortComplex.ShortExact.extClass_naturality
    (torsorAugmentation_shortExact P) (torsorAugmentation_shortExact Q)
    (torsorAugmentationComplexMap r)
  change (torsorAugmentation_shortExact P).extClass.comp
      (Abelian.Ext.mk₀ (torsorKernelSheafMap r)) (add_zero 1) =
    (Abelian.Ext.mk₀ (𝟙 _)).comp (torsorAugmentation_shortExact Q).extClass (zero_add 1) at h
  rw [Abelian.Ext.mk₀_id_comp] at h
  rw [torsorExtClass_eq P, torsorExtClass_eq Q]
  change ((torsorAugmentation_shortExact P).extClass.comp
    (Abelian.Ext.mk₀ (torsorDifferenceSheafMap P)) (add_zero 1)).comp
      (Abelian.Ext.mk₀ q) (add_zero 1) = _
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    ← torsorDifferenceSheafMap_naturality r, ← Abelian.Ext.mk₀_comp_mk₀,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, h]

/-- Equivariant sheaf isomorphisms preserve the canonical Ext class. -/
theorem torsorExtClass_iso {Q : Torsor L} (e : Torsor.Iso P Q) : torsorExtClass P =
  torsorExtClass Q := by
  have h := torsorExtClass_naturality
    (q := 𝟙 L) (P := P) (Q := Q) (⟨e.carrierIso.hom, e.equivariant⟩ : Torsor.Hom (𝟙 L) P Q)
  simpa only [coefficientMap_id, AddMonoidHom.id_apply] using h

/-- Descent of the canonical map to the actual sheaf-torsor isomorphism classes. -/
def torsorClassToH1 (L : AbelianSheaf.{u, u + 1} X) : TorsorClass L → H1Etale X L :=
  Quotient.lift torsorExtClass (fun _ _ ⟨e⟩ => torsorExtClass_iso e)

@[simp] theorem torsorClassToH1_mk (P : Torsor L) :
    torsorClassToH1 L (Quotient.mk (Torsor.isomorphicSetoid L) P) = torsorExtClass P := rfl

/-- The exact retained general theorem boundary of Stacks 03AJ, Lemma 21.4.3:
bijectivity of the constructed extension/boundary class map.
Source: https://stacks.math.columbia.edu/tag/03AJ (inspected 2026-10-09). This record does
not assume additivity, scheme naturality, or any fundamental-group comparison. -/
structure Stacks03AJ (X : Scheme.{u})
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] : Prop where
  bijective (L : AbelianSheaf.{u, u + 1} X) : Function.Bijective (torsorClassToH1 L)

/-- The canonical torsor-class bijection under precisely Stacks 03AJ. An
additive equivalence still requires the separate contracted-sum construction. -/
def torsorClassEquiv (h : Stacks03AJ.{u, w} X) (L : AbelianSheaf.{u, u + 1} X) :
    TorsorClass L ≃ H1Etale X L :=
  Equiv.ofBijective (torsorClassToH1 L) (h.bijective L)

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 00a6113831601e70056182abbffd3d8c9f6045e9d1904f2fe40fa851629f0d33.
Definitions, hypotheses and universes are retained modulo native names. -/
