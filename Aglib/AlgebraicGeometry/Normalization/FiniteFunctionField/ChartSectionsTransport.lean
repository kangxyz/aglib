/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.FiniteFunctionField.ChartSections

/-!
# Original normalization charts under equality of generic maps

The original generic-chart field iso and normalization-section equivalence are
transported once along the specified equality of maps. Native mapped closures
retain their coefficient, ambient and affine-restriction laws. The specified
target ring has an independent universe and its original chart actions.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteFunctionField

universe uR uS uF uG

private theorem mapIntegralClosure_trans_val_comp
    {R : Type uR} {S : Type uS} {F : Type uF} {G : Type uG}
    [CommRing R] [CommRing S] [CommRing F] [CommRing G]
    [Algebra R S] [Algebra R F] [Algebra R G]
    (e : S ≃ₐ[R] integralClosure R F) (E : F ≃ₐ[R] G) :
    (integralClosure R G).val.toRingHom.comp
        (e.trans E.mapIntegralClosure).toRingHom =
      E.toRingHom.comp
        ((integralClosure R F).val.toRingHom.comp e.toRingHom) := by
  apply RingHom.ext
  intro x
  exact AlgEquiv.coe_mapIntegralClosure E (e x)

private theorem mapIntegralClosure_comp_scalarExtensionHom
    {R : Type uR} {S : Type uS} {F : Type uF} {G : Type uG}
    [CommRing R] [CommRing S] [CommRing F] [CommRing G]
    [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
    [Algebra R G] [Algebra S G] [IsScalarTower R S G]
    (E_R : F ≃ₐ[R] G) (E_S : F ≃ₐ[S] G) (hE : E_R.toRingHom = E_S.toRingHom) :
    E_S.mapIntegralClosure.toRingHom.comp
        (integralClosure.scalarExtensionHom R S F).toRingHom =
      (integralClosure.scalarExtensionHom R S G).toRingHom.comp
        E_R.mapIntegralClosure.toRingHom := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change E_S (x : F) = E_R (x : F)
  exact (RingHom.congr_fun hE (x : F)).symm

universe u vG

variable (X : Scheme.{u}) [IsIntegral X]
  (F : Type u) [Field F] [Algebra X.functionField F]
  (f : Spec (.of F) ⟶ X) [QuasiCompact f] [QuasiSeparated f]
  (hf : f = genericMap X F)

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The SAME original generic-chart field iso, transported along the specified map equality. -/
def chartFieldIsoOfEq (U : X.Opens) [Nonempty U] :
    Γ(Spec (.of F), f ⁻¹ᵁ U) ≅ CommRingCat.of F :=
  Eq.ndrec (motive := fun g : Spec (.of F) ⟶ X =>
      Γ(Spec (.of F), g ⁻¹ᵁ U) ≅ CommRingCat.of F)
    (chartFieldIso X F U) hf.symm

/-- The SAME original normalization-section equivalence, with the original QC/QS witnesses. -/
def normalizationSectionsEquivOfEq
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := chartAmbientAlgebra X F U
    letI := (f.fromNormalization.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) F := by
  let := chartAmbientAlgebra X F U
  exact (Eq.ndrec
    (motive := fun g : Spec (.of F) ⟶ X =>
      ∀ (hq : QuasiCompact g) (hr : QuasiSeparated g),
        letI := hq
        letI := hr
        letI := (g.fromNormalization.app U).hom.toAlgebra
        Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
          integralClosure Γ(X, U) F)
    (fun _ _ => normalizationSectionsEquiv X F U hU) hf.symm)
    (inferInstance : QuasiCompact f) (inferInstance : QuasiSeparated f)

/-- Compose that SAME transported section equivalence with the native mapped closure. -/
def normalizationSectionsEquivMapOfEq
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (G : Type vG) [CommRing G] [Algebra Γ(X, U) G]
    (E : letI := chartAmbientAlgebra X F U; F ≃ₐ[Γ(X, U)] G) :
    letI := (f.fromNormalization.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) G := by
  let := chartAmbientAlgebra X F U
  let := (f.fromNormalization.app U).hom.toAlgebra
  exact (normalizationSectionsEquivOfEq X F f hf U hU).trans E.mapIntegralClosure

/-- The original structural section map becomes the literal mapped-closure coefficient map. -/
theorem normalizationSectionsEquivMapOfEq_coefficients
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (G : Type vG) [CommRing G] [Algebra Γ(X, U) G]
    (E : letI := chartAmbientAlgebra X F U; F ≃ₐ[Γ(X, U)] G) :
    (normalizationSectionsEquivMapOfEq X F f hf U hU G E).toRingHom.comp
        (f.fromNormalization.app U).hom =
      algebraMap Γ(X, U) (integralClosure Γ(X, U) G) := by
  let := (f.fromNormalization.app U).hom.toAlgebra
  apply RingHom.ext
  intro r
  exact (normalizationSectionsEquivMapOfEq X F f hf U hU G E).commutes r

/-- The complete mapped-closure ambient equation retains both original transported maps. -/
theorem normalizationSectionsEquivMapOfEq_val_comp
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (G : Type vG) [CommRing G] [Algebra Γ(X, U) G]
    (E : letI := chartAmbientAlgebra X F U; F ≃ₐ[Γ(X, U)] G) :
    (integralClosure Γ(X, U) G).val.toRingHom.comp
        (normalizationSectionsEquivMapOfEq X F f hf U hU G E).toRingHom =
      E.toRingHom.comp ((chartFieldIsoOfEq X F f hf U).hom.hom.comp
        (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by
          simp only [← Scheme.Hom.comp_preimage,
            Scheme.Hom.toNormalization_fromNormalization, le_refl])).hom) := by
  subst f
  let := chartAmbientAlgebra X F U
  let := ((fromNormalization X F).app U).hom.toAlgebra
  have hValue := congrArg
    (fun q : Γ(normalization X F, (fromNormalization X F) ⁻¹ᵁ U) →+* F =>
      E.toRingHom.comp q)
    (normalizationSectionsEquiv_val_comp X F U hU)
  have hComposition := mapIntegralClosure_trans_val_comp
    (normalizationSectionsEquiv X F U hU) E
  have hFinal := hComposition.trans hValue
  dsimp only [normalizationSectionsEquivMapOfEq, normalizationSectionsEquivOfEq,
    chartFieldIsoOfEq]
  simp only [normalization, fromNormalization, toNormalization] at hFinal ⊢
  exact hFinal

/-- Evaluate the SAME mapped chart construction in its specified original field-function view. -/
theorem normalizationSectionsEquivMapOfEq_val
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (G : Type vG) [CommRing G] [Algebra Γ(X, U) G]
    (E : letI := chartAmbientAlgebra X F U; F ≃ₐ[Γ(X, U)] G)
    (v : F → G) (hE : (E : F → G) = v)
    (c : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)) :
    (normalizationSectionsEquivMapOfEq X F f hf U hU G E c : G) =
      v ((chartFieldIsoOfEq X F f hf U).hom
        (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by
          simp only [← Scheme.Hom.comp_preimage,
            Scheme.Hom.toNormalization_fromNormalization, le_refl]) c)) := by
  let := (f.fromNormalization.app U).hom.toAlgebra
  have hValue := RingHom.congr_fun
    (normalizationSectionsEquivMapOfEq_val_comp X F f hf U hU G E) c
  exact hValue.trans (congrFun hE _)

/-- Original affine restrictions commute with the SAME transported section equivalences. -/
theorem normalizationSectionsEquivOfEq_restriction
    (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := chartAmbientAlgebra X F U
    letI := chartAmbientAlgebra X F V
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI := chartAmbientRestriction_isScalarTower X F U V h
    (normalizationSectionsEquivOfEq X F f hf V hV).toRingHom.comp
        (f.normalization.presheaf.map
          (homOfLE (f.fromNormalization.preimage_mono h)).op).hom =
      (integralClosure.scalarExtensionHom Γ(X, U) Γ(X, V) F).toRingHom.comp
        (normalizationSectionsEquivOfEq X F f hf U hU).toRingHom := by
  subst f
  dsimp only [normalizationSectionsEquivOfEq]
  exact normalizationSectionsEquiv_restriction X F U V h hU hV

/-- The complete mapped restriction uses the SAME ambient map and original scalar tower. -/
theorem normalizationSectionsEquivMapOfEq_restriction
    (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (G : Type vG) [CommRing G] [Algebra Γ(X, U) G] [Algebra Γ(X, V) G]
    (E_U : letI := chartAmbientAlgebra X F U; F ≃ₐ[Γ(X, U)] G)
    (E_V : letI := chartAmbientAlgebra X F V; F ≃ₐ[Γ(X, V)] G)
    (hG : letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
      IsScalarTower Γ(X, U) Γ(X, V) G)
    (hE : E_U.toRingHom = E_V.toRingHom) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI := hG
    (normalizationSectionsEquivMapOfEq X F f hf V hV G E_V).toRingHom.comp
        (f.normalization.presheaf.map
          (homOfLE (f.fromNormalization.preimage_mono h)).op).hom =
      (integralClosure.scalarExtensionHom Γ(X, U) Γ(X, V) G).toRingHom.comp
        (normalizationSectionsEquivMapOfEq X F f hf U hU G E_U).toRingHom := by
  let := chartAmbientAlgebra X F U
  let := chartAmbientAlgebra X F V
  let := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let := chartAmbientRestriction_isScalarTower X F U V h
  let := hG
  let := (f.fromNormalization.app U).hom.toAlgebra
  let := (f.fromNormalization.app V).hom.toAlgebra
  have hNative := normalizationSectionsEquivOfEq_restriction X F f hf U V h hU hV
  have hMapped := mapIntegralClosure_comp_scalarExtensionHom E_U E_V hE
  dsimp only [normalizationSectionsEquivMapOfEq]
  change
    ((normalizationSectionsEquivOfEq X F f hf V hV).toRingEquiv.trans
      E_V.mapIntegralClosure.toRingEquiv).toRingHom.comp
        (f.normalization.presheaf.map
          (homOfLE (f.fromNormalization.preimage_mono h)).op).hom =
      (integralClosure.scalarExtensionHom Γ(X, U) Γ(X, V) G).toRingHom.comp
        ((normalizationSectionsEquivOfEq X F f hf U hU).toRingEquiv.trans
          E_U.mapIntegralClosure.toRingEquiv).toRingHom
  rw [RingEquiv.toRingHom_trans, RingEquiv.toRingHom_trans,
    RingHom.comp_assoc, hNative, ← RingHom.comp_assoc, hMapped, RingHom.comp_assoc]

include hf in
/-- The SAME original principal section restriction is localization, even if its open is empty. -/
theorem normalizationSections_isLocalization_basicOpen_of_eq
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (t : Γ(X, U)) :
    letI := (f.normalization.presheaf.map
      (homOfLE (f.fromNormalization.preimage_mono (X.basicOpen_le t))).op).hom.toAlgebra
    IsLocalization.Away (f.fromNormalization.app U t)
      Γ(f.normalization, f.fromNormalization ⁻¹ᵁ X.basicOpen t) := by
  subst f
  exact normalizationSections_isLocalization_basicOpen X F U hU t

end AlgebraicGeometry.Scheme.FiniteFunctionField
