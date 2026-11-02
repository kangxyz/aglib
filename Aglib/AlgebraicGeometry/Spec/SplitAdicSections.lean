/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.AdicSectionRetraction
public import Aglib.AlgebraicGeometry.Spec.SplitQuotientOpen
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NativeScalarSections
public import Aglib.AlgebraicGeometry.FunctionField.SplitSections

/-! # Actual scalar sections on arbitrary split-adic opens -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (i : A →+* B) (ε : B →+* A) (hε : ε.comp i = RingHom.id A)
  (V : (Spec (.of B)).Opens)

/-- The original intersection with the section, without a replacement open. -/
abbrev splitSectionOpen := Spec.map (CommRingCat.ofHom ε) ⁻¹ᵁ V

local notation "U" => splitSectionOpen ε V
local notation "I" => RingHom.ker ε

include hε in
/-- Flat scalar base change and the actual open comparison give bijectivity
on every literal kernel-power thickening; it is not an extra premise. -/
theorem splitAdicSectionScalar_bijective
    [QuasiCompact (U).ι] [QuasiSeparated (U).ι]
    (hU : Function.Bijective (affineScalarMap (U).ι))
    (hflat : ∀ n, ((Ideal.Quotient.mk (I ^ n)).comp i).Flat) (n : ℕ) :
    Function.Bijective (adicSectionScalar V.ι I n) := by
  let a := splitQuotientScalar i ε n
  let q := pullback.snd (U).ι a
  have hq := Cohomology.scalarSections_bijective_of_flat_of_isPullback
    (pullback.fst (U).ι a) ((Ideal.Quotient.mk (I ^ n)).comp i) q (U).ι
    (IsPullback.of_hasPullback (U).ι a) (hflat n) hU
  let e := splitQuotientOpenIso i ε hε V n
  have he : e.hom ≫ q = Modules.idealThickeningStructure V.ι (I ^ n) :=
    splitQuotientOpenIso_hom_snd i ε hε V n
  have hs : e.hom.appTop.hom.comp (affineScalarMap q) = adicSectionScalar V.ι I n := by
    change (((ΓSpecIso (.of (B ⧸ I ^ n))).inv ≫ q.appTop) ≫ e.hom.appTop).hom = _
    rw [Category.assoc, ← Hom.comp_appTop, he]
    rfl
  rw [← hs]
  have hE : Function.Bijective e.hom.appTop.hom := by
    change Function.Bijective (Scheme.Γ.map e.hom.op).hom
    exact ConcreteCategory.bijective_of_isIso (Scheme.Γ.map e.hom.op)
  exact hE.comp hq

/-- Original open global sections agree with ambient sections through the native
open restriction isomorphism, retaining the actual scalar map. -/
theorem affineScalarMap_topIso (V : (Spec (.of B)).Opens) :
    V.topIso.hom.hom.comp (affineScalarMap V.ι) = hartogsScalarMap B V := by
  change (((ΓSpecIso (.of B)).inv ≫ V.ι.appTop) ≫ V.topIso.hom).hom = _
  have hv : V.ι.appTop ≫ V.topIso.hom =
      (Spec (.of B)).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    simp only [Opens.ι_appTop, Opens.topIso_hom]
    congr 1
  rw [Category.assoc, hv]
  rfl

variable [hqc : QuasiCompact (splitSectionOpen ε V).ι]
  [hqs : QuasiSeparated (splitSectionOpen ε V).ι]
  (hU : Function.Bijective (affineScalarMap (splitSectionOpen ε V).ι))
  (hflat : ∀ n, ((Ideal.Quotient.mk ((RingHom.ker ε) ^ n)).comp i).Flat)
  [IsAdicComplete (RingHom.ker ε) B]

/-- The constructed retraction on the original ambient open sections. -/
def splitAdicSectionsRetraction : Γ(Spec (.of B), V) →+* B := by
  have H := @splitAdicSectionScalar_bijective A B ‹CommRing A› ‹CommRing B› i ε hε V
  have H1 := @H hqc
  have H2 := @H1 hqs
  have H3 := H2 hU
  have hb := H3 hflat
  let r := adicSectionRetraction V.ι I hb
  exact r.comp V.topIso.inv.hom

/-- The whole original scalar composite of the constructed retraction. -/
theorem splitAdicSectionsRetraction_scalar :
    (splitAdicSectionsRetraction i ε hε V hU hflat).comp (hartogsScalarMap B V) =
      RingHom.id B := by
  rw [← affineScalarMap_topIso V]
  ext b
  change adicSectionRetraction V.ι I
    (splitAdicSectionScalar_bijective i ε hε V hU hflat)
    (V.topIso.inv.hom (V.topIso.hom.hom (affineScalarMap V.ι b))) = b
  simp only [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  exact RingHom.congr_fun (adicSectionRetraction_scalar V.ι I
    (splitAdicSectionScalar_bijective i ε hε V hU hflat)) b

include hε hU hflat in
/-- On a domain, the original nonempty open scalar map is therefore bijective.
The retraction is constructed above, not supplied as a hypothesis. -/
theorem splitAdicSections_bijective [IsDomain B] [Nonempty V] :
    Function.Bijective (hartogsScalarMap B V) :=
  hartogsScalarMap_bijective_of_retraction B V
    (splitAdicSectionsRetraction i ε hε V hU hflat)
    (splitAdicSectionsRetraction_scalar i ε hε V hU hflat)

/-- The full original section-ring equivalence with the constructed inverse. -/
def splitAdicSectionsEquiv [IsDomain B] [Nonempty V] : B ≃+* Γ(Spec (.of B), V) :=
  splitSectionsEquiv B V (splitAdicSectionsRetraction i ε hε V hU hflat)
    (splitAdicSectionsRetraction_scalar i ε hε V hU hflat)

end AlgebraicGeometry.Scheme
