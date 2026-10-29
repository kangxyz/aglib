/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Classification
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorCohomology

/-! # The original etale torsor class map

The actual maps and quotient specialize the proved generic-site producers.
The historical classification record is retained only for interface compatibility;
the equivalence uses the single proved actual-extension inverse.
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

/-- The original coefficient-relative morphism is the selected generic Hom. -/
abbrev Torsor.Hom (q : L ⟶ M) (P : Torsor L) (Q : Torsor M) :=
  CategoryTheory.Sheaf.Torsor.Hom q P Q

/-- The original constructor of a coefficient-relative torsor map. -/
abbrev Torsor.Hom.mk {q : L ⟶ M} {P : Torsor L} {Q : Torsor M} :=
  CategoryTheory.Sheaf.Torsor.Hom.mk (q := q) (P := P) (Q := Q)

/-- The original carrier-map projection. -/
abbrev Torsor.Hom.map {q : L ⟶ M} {P : Torsor L} {Q : Torsor M}
    (r : Torsor.Hom q P Q) := CategoryTheory.Sheaf.Torsor.Hom.map r

/-- The original equivariance projection. -/
abbrev Torsor.Hom.equivariant {q : L ⟶ M} {P : Torsor L} {Q : Torsor M}
    (r : Torsor.Hom q P Q) := CategoryTheory.Sheaf.Torsor.Hom.equivariant r

variable {q : L ⟶ M} {P : Torsor L} {Q : Torsor M}

/-- The free-abelian presheaf morphism induced by a torsor morphism. -/
abbrev torsorFreePresheafMap (r : Torsor.Hom q P Q) : torsorFreePresheaf P ⟶ torsorFreePresheaf Q :=
  CategoryTheory.Sheaf.torsorFreePresheafMap r

/-- Torsor morphisms commute with the actual augmentation. -/
theorem torsorFreePresheafMap_augmentation (r : Torsor.Hom q P Q) :
    torsorFreePresheafMap r ≫ torsorAugmentationPresheaf Q = torsorAugmentationPresheaf P :=
  CategoryTheory.Sheaf.torsorFreePresheafMap_augmentation r

/-- The induced map on actual augmentation kernels is the universal kernel lift. -/
abbrev torsorKernelPresheafMap (r : Torsor.Hom q P Q) :
    torsorKernelPresheaf P ⟶ torsorKernelPresheaf Q :=
  CategoryTheory.Sheaf.torsorKernelPresheafMap r

@[reassoc] theorem torsorKernelPresheafMap_inclusion (r : Torsor.Hom q P Q) :
    torsorKernelPresheafMap r ≫ torsorKernelInclusion Q =
      torsorKernelInclusion P ≫ torsorFreePresheafMap r :=
  CategoryTheory.Sheaf.torsorKernelPresheafMap_inclusion r

/-- Explicit restriction/coefficient formula for the universal kernel map. -/
theorem torsorKernelPresheafMap_apply (r : Torsor.Hom q P Q) (U : X.Etaleᵒᵖ)
    (x : AddAction.TorsorAugmentation.AugmentationKernel (P.carrier.obj.obj U)) :
    (torsorKernelPresheafMap r).app U x =
      AddAction.TorsorAugmentation.kernelMap (r.map.hom.app U) x :=
  CategoryTheory.Sheaf.torsorKernelPresheafMap_apply r U x

/-- Naturality of the canonical torsor-difference morphism before sheafification. -/
theorem torsorKernelDifference_naturality (r : Torsor.Hom q P Q) :
    torsorKernelPresheafMap r ≫ torsorKernelDifference Q =
      torsorKernelDifference P ≫ q.hom :=
  CategoryTheory.Sheaf.torsorKernelDifference_naturality r

/-- The map on sheafified augmentation kernels. -/
abbrev torsorKernelSheafMap (r : Torsor.Hom q P Q) : torsorKernelSheaf P ⟶ torsorKernelSheaf Q :=
  CategoryTheory.Sheaf.torsorKernelSheafMap r

/-- The map on free abelian sheaves obtained by sheafifying the map induced by the torsor
morphism. -/
abbrev torsorFreeSheafMap (r : Torsor.Hom q P Q) : torsorFreeSheaf P ⟶ torsorFreeSheaf Q :=
  CategoryTheory.Sheaf.torsorFreeSheafMap r

/-- Morphism of the actual augmentation short exact sequences. -/
abbrev torsorAugmentationComplexMap (r : Torsor.Hom q P Q) :
    torsorAugmentationComplex P ⟶ torsorAugmentationComplex Q :=
  CategoryTheory.Sheaf.torsorAugmentationComplexMap r

/-- The canonical difference map commutes with sheafification and coefficient maps. -/
theorem torsorDifferenceSheafMap_naturality (r : Torsor.Hom q P Q) :
    torsorKernelSheafMap r ≫ torsorDifferenceSheafMap Q = torsorDifferenceSheafMap P ≫ q :=
  CategoryTheory.Sheaf.torsorDifferenceSheafMap_naturality r

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Naturality of the constructed torsor class for every actual equivariant
sheaf map with the specified coefficient map. -/
theorem torsorExtClass_naturality (r : Torsor.Hom q P Q) :
    coefficientMap q (torsorExtClass P) = torsorExtClass Q :=
  CategoryTheory.Sheaf.torsorExtClass_naturality r

/-- Equivariant sheaf isomorphisms preserve the canonical Ext class. -/
theorem torsorExtClass_iso {Q : Torsor L} (e : Torsor.Iso P Q) : torsorExtClass P =
  torsorExtClass Q :=
  CategoryTheory.Sheaf.torsorExtClass_iso e

/-- Descent of the canonical map to the actual sheaf-torsor isomorphism classes. -/
abbrev torsorClassToH1 (L : AbelianSheaf.{u, u + 1} X) : TorsorClass L → H1Etale X L :=
  CategoryTheory.Sheaf.torsorClassToH1 L

@[simp] theorem torsorClassToH1_mk (P : Torsor L) :
    torsorClassToH1 L (Quotient.mk (Torsor.isomorphicSetoid L) P) = torsorExtClass P :=
  CategoryTheory.Sheaf.torsorClassToH1_mk P

/-- The exact retained general theorem boundary of Stacks 03AJ, Lemma 21.4.3:
bijectivity of the constructed extension/boundary class map.
Source: https://stacks.math.columbia.edu/tag/03AJ (inspected 2026-10-09). This record does
not assume additivity, scheme naturality, or any fundamental-group comparison. -/
structure Stacks03AJ (X : Scheme.{u})
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] : Prop where
  bijective (L : AbelianSheaf.{u, u + 1} X) : Function.Bijective (torsorClassToH1 L)

/-- The legacy proof argument is retained; the inverse is the single proved generic inverse. -/
def torsorClassEquiv (h : Stacks03AJ.{u, w} X) (L : AbelianSheaf.{u, u + 1} X) :
    TorsorClass L ≃ H1Etale X L :=
  (fun _ : Stacks03AJ.{u, w} X => CategoryTheory.Sheaf.torsorClassEquiv L) h

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 00a6113831601e70056182abbffd3d8c9f6045e9d1904f2fe40fa851629f0d33.
Definitions, hypotheses and universes are retained modulo native names. -/
