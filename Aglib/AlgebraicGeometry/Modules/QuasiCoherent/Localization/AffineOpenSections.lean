/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Denominator clearing on actual affine opens

The canonical map `Spec Γ(X,V) → X` transports the original section-localization statements
to an affine open of an arbitrary scheme. The comparison is the original restriction
adjunction unit, with its actual ring maps and scalar actions retained explicitly.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections

variable {X : Scheme.{u}} (M : X.Modules) {V W : X.Opens}

/-- On a subopen of the original affine open, the canonical affine chart map takes
restricted functions to the original affine structural constants. -/
theorem fromSpec_restriction (hV : IsAffineOpen V) (hWV : W ≤ V) :
    X.presheaf.map (homOfLE hWV).op ≫ hV.fromSpec.app W =
      (Scheme.ΓSpecIso Γ(X, V)).inv ≫
        (Spec Γ(X, V)).presheaf.map (homOfLE le_top).op := by
  rw [hV.fromSpec.naturality, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  congr 1

/-- The pointwise form keeps the original function and its actual restriction map. -/
theorem fromSpec_restriction_apply (hV : IsAffineOpen V) (hWV : W ≤ V) (r : Γ(X, V)) :
    hV.fromSpec.app W (X.presheaf.map (homOfLE hWV).op r) =
      (Spec Γ(X, V)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X, V)).inv r) := by
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (fromSpec_restriction hV hWV)) r
  exact h

/-- On an open contained in the affine chart range, the actual module restriction unit
is an isomorphism on sections. -/
theorem isIso_restrictionUnit_app (hV : IsAffineOpen V) (hWV : W ≤ V) :
    IsIso (((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app M).app W) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have h : hV.fromSpec ''ᵁ (hV.fromSpec ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hV.opensRange_fromSpec,
      inf_eq_right.mpr hWV]
  have he : homOfLE (hV.fromSpec.image_preimage_le W) = eqToHom h := Subsingleton.elim _ _
  rw [he]
  infer_instance

/-- The canonical actual section isomorphism associated with the affine chart restriction
unit, for every contained open. -/
def restrictionUnitIso (hV : IsAffineOpen V) (hWV : W ≤ V) :
    Γ(M, W) ≅ Γ(M.restrict hV.fromSpec, hV.fromSpec ⁻¹ᵁ W) := by
  letI := isIso_restrictionUnit_app M hV hWV
  exact asIso (((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app M).app W)

/-- The actual restriction unit preserves the original affine-open function action,
where the target has its native `Spec Γ(X,V)` module structure. -/
theorem restrictionUnit_smul (hV : IsAffineOpen V) (hWV : W ≤ V) (r : Γ(X, V))
    (s : Γ(M, W)) :
    ((restrictionUnitIso M hV hWV).hom)
        (X.presheaf.map (homOfLE hWV).op r • s) =
      r • ((restrictionUnitIso M hV hWV).hom s) := by
  change (((Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app M).app W)
      (X.presheaf.map (homOfLE hWV).op r • s) = _
  rw [Scheme.Modules.Hom.app_smul]
  change hV.fromSpec.app W (X.presheaf.map (homOfLE hWV).op r) •
      ((restrictionUnitIso M hV hWV).hom s) =
    r • ((restrictionUnitIso M hV hWV).hom s)
  rw [Scheme.Modules.smul_Spec_def, fromSpec_restriction_apply]
  have htop : homOfLE (le_top : hV.fromSpec ⁻¹ᵁ W ≤ ⊤) =
      (hV.fromSpec ⁻¹ᵁ W).leTop := Subsingleton.elim _ _
  rw [htop]

/-- Original sections on the affine open are the global sections on its canonical spectrum,
through the actual restriction unit. -/
def toSpecTopSectionsIso (hV : IsAffineOpen V) :
    Γ(M, V) ≅ Γ(M.restrict hV.fromSpec, ⊤) :=
  restrictionUnitIso M hV le_rfl ≪≫
    (M.restrict hV.fromSpec).presheaf.mapIso (eqToIso hV.fromSpec_preimage_self.symm).op

/-- Original sections on the nonvanishing open are sections on the corresponding actual
principal open of the canonical affine spectrum. -/
def toSpecBasicOpenSectionsIso (hV : IsAffineOpen V) (f : Γ(X, V)) :
    Γ(M, X.basicOpen f) ≅ Γ(M.restrict hV.fromSpec, PrimeSpectrum.basicOpen f) :=
  restrictionUnitIso M hV (X.basicOpen_le f) ≪≫
    (M.restrict hV.fromSpec).presheaf.mapIso
      (eqToIso (hV.fromSpec_preimage_basicOpen f).symm).op

/-- The affine-open section isomorphism preserves the original affine section-ring action. -/
theorem toSpecTopSectionsIso_smul (hV : IsAffineOpen V) (r : Γ(X, V)) (s : Γ(M, V)) :
    (toSpecTopSectionsIso M hV).hom (r • s) = r • (toSpecTopSectionsIso M hV).hom s := by
  have hu : (restrictionUnitIso M hV le_rfl).hom (r • s) =
      r • (restrictionUnitIso M hV le_rfl).hom s := by
    simpa using restrictionUnit_smul M hV le_rfl r s
  change (M.restrict hV.fromSpec).presheaf.map (eqToHom hV.fromSpec_preimage_self.symm).op
      ((restrictionUnitIso M hV le_rfl).hom (r • s)) = _
  rw [hu, Scheme.Modules.map_smul_Spec]
  rfl

/-- The canonical affine-open comparison as a linear equivalence over the original
affine section ring, with its native structural action on spectrum sections. -/
def toSpecTopSectionsLinearEquiv (hV : IsAffineOpen V) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(M.restrict hV.fromSpec, ⊤) where
  __ := (toSpecTopSectionsIso M hV).addCommGroupIsoToAddEquiv
  map_smul' := toSpecTopSectionsIso_smul M hV

/-- The affine-open comparison retains the original coefficient map and its actual
restriction to the canonical spectrum. -/
theorem toSpecTopSectionsIso_naturality {N : X.Modules} (φ : M ⟶ N)
    (hV : IsAffineOpen V) :
    φ.app V ≫ (toSpecTopSectionsIso N hV).hom =
      (toSpecTopSectionsIso M hV).hom ≫
        ((Scheme.Modules.restrictFunctor hV.fromSpec).map φ).app ⊤ := by
  let f := hV.fromSpec
  let φ' := (Scheme.Modules.restrictFunctor f).map φ
  let η := (Scheme.Modules.restrictAdjunction f).unit
  have hu : φ.app V ≫ (η.app N).app V =
      (η.app M).app V ≫ φ'.app (f ⁻¹ᵁ V) := by
    exact congrArg (fun ψ : M ⟶ (Scheme.Modules.pushforward f).obj (N.restrict f) =>
      ψ.app V) (η.naturality φ)
  let a : op (f ⁻¹ᵁ V) ⟶ op (⊤ : (Spec Γ(X, V)).Opens) :=
    (eqToHom hV.fromSpec_preimage_self.symm).op
  have hn : (M.restrict f).presheaf.map a ≫ φ'.app ⊤ =
      φ'.app (f ⁻¹ᵁ V) ≫ (N.restrict f).presheaf.map a :=
    φ'.mapPresheaf.naturality a
  change φ.app V ≫ ((η.app N).app V ≫ (N.restrict f).presheaf.map a) =
    ((η.app M).app V ≫ (M.restrict f).presheaf.map a) ≫ φ'.app ⊤
  rw [← Category.assoc, hu, Category.assoc, Category.assoc, hn]

/-- The principal-open comparison retains the actual restriction of the original affine
function as its scalar action. -/
theorem toSpecBasicOpenSectionsIso_smul (hV : IsAffineOpen V) (f r : Γ(X, V))
    (s : Γ(M, X.basicOpen f)) :
    (toSpecBasicOpenSectionsIso M hV f).hom
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op r • s) =
      r • (toSpecBasicOpenSectionsIso M hV f).hom s := by
  change (M.restrict hV.fromSpec).presheaf.map
      (eqToHom (hV.fromSpec_preimage_basicOpen f).symm).op
        ((restrictionUnitIso M hV (X.basicOpen_le f)).hom
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op r • s)) = _
  rw [restrictionUnit_smul, Scheme.Modules.map_smul_Spec]
  rfl

/-- The canonical affine-open section comparisons preserve the actual restriction to the
nonvanishing open. -/
theorem toSpecSectionsIso_restriction (hV : IsAffineOpen V) (f : Γ(X, V)) :
    M.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ (toSpecBasicOpenSectionsIso M hV f).hom =
      (toSpecTopSectionsIso M hV).hom ≫
        (M.restrict hV.fromSpec).presheaf.map (PrimeSpectrum.basicOpen f).leTop.op := by
  let N := M.restrict hV.fromSpec
  let η := (Scheme.Modules.restrictAdjunction hV.fromSpec).unit.app M
  have hn : M.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ η.app (X.basicOpen f) =
      η.app V ≫ N.presheaf.map
        ((Opens.map hV.fromSpec.base).map (homOfLE (X.basicOpen_le f))).op :=
    η.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op
  change M.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫
      (η.app (X.basicOpen f) ≫ N.presheaf.map
        (eqToHom (hV.fromSpec_preimage_basicOpen f).symm).op) =
    (η.app V ≫ N.presheaf.map (eqToHom hV.fromSpec_preimage_self.symm).op) ≫
      N.presheaf.map (PrimeSpectrum.basicOpen f).leTop.op
  rw [← Category.assoc, hn, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (fun k => η.app V ≫ N.presheaf.map k)
  exact Subsingleton.elim _ _

/-- Every section on the nonvanishing open of an affine open extends after multiplication
by a power of the original function. Quasicoherence is required only on that affine chart. -/
theorem exists_power_mul_eq_restriction (hV : IsAffineOpen V)
    [(M.restrict hV.fromSpec).IsQuasicoherent] (f : Γ(X, V)) (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  let N : (Spec Γ(X, V)).Modules := M.restrict hV.fromSpec
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj N) :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance
  let : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom := hlocal f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom f
      ((toSpecBasicOpenSectionsIso M hV f).hom s)
  refine ⟨n, (toSpecTopSectionsIso M hV).inv t, ?_⟩
  apply (toSpecBasicOpenSectionsIso M hV f).addCommGroupIsoToAddEquiv.injective
  have hres : (toSpecBasicOpenSectionsIso M hV f).hom
      (M.presheaf.map (homOfLE (X.basicOpen_le f)).op ((toSpecTopSectionsIso M hV).inv t)) =
      N.presheaf.map (PrimeSpectrum.basicOpen f).leTop.op t := by
    have h := ConcreteCategory.congr_hom (toSpecSectionsIso_restriction M hV f)
      ((toSpecTopSectionsIso M hV).inv t)
    simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using h
  have hsmul := toSpecBasicOpenSectionsIso_smul M hV f (f ^ n) s
  rw [map_pow] at hsmul
  exact hres.trans (ht.symm.trans hsmul.symm)

/-- If an actual section becomes zero after restriction to the nonvanishing open, a power
of the original affine function annihilates it. No quasicoherence outside the chart is used. -/
theorem exists_power_smul_eq_zero (hV : IsAffineOpen V)
    [(M.restrict hV.fromSpec).IsQuasicoherent] (f : Γ(X, V)) (t : Γ(M, V))
    (ht : M.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  let N : (Spec Γ(X, V)).Modules := M.restrict hV.fromSpec
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj N) :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance
  let : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom := hlocal f
  have hz : ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom
      ((toSpecTopSectionsIso M hV).hom t) = 0 := by
    have h := ConcreteCategory.congr_hom (toSpecSectionsIso_restriction M hV f) t
    change (toSpecBasicOpenSectionsIso M hV f).hom
      (M.presheaf.map (homOfLE (X.basicOpen_le f)).op t) =
      N.presheaf.map (PrimeSpectrum.basicOpen f).leTop.op
        ((toSpecTopSectionsIso M hV).hom t) at h
    rw [ht, map_zero] at h
    exact h.symm
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq
    (f := ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom) f
    (x := (toSpecTopSectionsIso M hV).hom t) (y := 0) (by simpa only [map_zero] using hz)
  rw [smul_zero] at hn
  refine ⟨n, ?_⟩
  apply (toSpecTopSectionsIso M hV).addCommGroupIsoToAddEquiv.injective
  change (toSpecTopSectionsIso M hV).hom (f ^ n • t) = (toSpecTopSectionsIso M hV).hom 0
  rw [toSpecTopSectionsIso_smul, map_zero]
  exact hn

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineOpenSections
