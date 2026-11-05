/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.WholeNormalOpenClass

/-! # The original selected generic zero on whole normal source models

The literal finite normal models, the original generic fibre comparison,
cover and point are retained. The original class is transported through the
same native pullback maps. Its marked source cover is extended globally,
without choosing a source prime or restricting the source base. Only the
coefficient base is restricted to a nonempty principal open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard

variable (A B k K F E : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [IsNoetherianRing A] [IsIntegrallyClosed A] [IsNoetherianRing B] [IsIntegrallyClosed B]
  [Field k] [Field K] [Field F] [Field E]
  [Algebra A B] [Algebra A k] [IsFractionRing A k]
  [Algebra A K] [Algebra B K] [IsFractionRing B K] [Algebra k K]
  [IsScalarTower A B K] [IsScalarTower A k K]
  [Algebra k F] [Module.Finite k F] [Algebra.IsSeparable k F]
  [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
  [Algebra k E] [IsScalarTower k K E]
  [Algebra A F] [IsScalarTower A k F]
  [Algebra A E] [Algebra B E] [IsScalarTower A k E]
  [IsScalarTower B K E] [IsScalarTower A B E]
  (a : F →ₐ[k] E)
  {X : Scheme.{u}} (p : X ⟶ Spec (.of A))
  (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)

/-- The two literal finite normal models and the original marked cover,
with a whole source section and actual coefficient-open zero. -/
def LiteralNormalWholeCoefficientOpen
    (Z : FiniteEtale (pullback (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F)))
    (z : Fiber (normalModelSection (pullback.snd p (Spec.algebraMap A k))
      (normalModelSection p σ hσ (Spec.algebraMap A k))
      (normalModelSection_over p σ hσ (Spec.algebraMap A k)) (Spec.algebraMap k F)) Z)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap A B)))]
    (M : AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap A B)))
    (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    : Prop :=
  let R := integralClosure A F
  let S := integralClosure B E
  let hR := SeparableBaseSquare.normal_finite_model A k F
  let hS := SeparableBaseSquare.normal_finite_model B K E
  letI : IsNoetherianRing R := hR.2.1
  letI : IsIntegrallyClosed R := hR.2.2.1
  letI : IsFractionRing R F := hR.2.2.2.1
  letI : IsFractionRing S E := hS.2.2.2.1
  let φ := SeparableBaseSquare.closureMap A B k F E a
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : Algebra R E := (a.toRingHom.comp (algebraMap R F)).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  let aR : F →ₐ[R] E := { a.toRingHom with commutes' := fun _ => rfl }
  let pR := pullback.snd p (Spec.algebraMap A R)
  let σR := normalModelSection p σ hσ (Spec.algebraMap A R)
  let hσR := normalModelSection_over p σ hσ (Spec.algebraMap A R)
  let ht : Spec.algebraMap R F ≫ Spec.algebraMap A R =
      Spec.algebraMap k F ≫ Spec.algebraMap A k := by
    simp only [Spec.algebraMap, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      ((IsScalarTower.algebraMap_eq A R F).symm.trans
        (IsScalarTower.algebraMap_eq A k F)))
  let i := normalGenericFibreIso p (Spec.algebraMap A k) (Spec.algebraMap A R)
    (Spec.algebraMap k F) (Spec.algebraMap R F) ht
  let ZR := (baseChange i.hom).obj Z
  let zR := normalGenericCoverPoint i Z (normalModelSection (pullback.snd p (Spec.algebraMap A k))
      (normalModelSection p σ hσ (Spec.algebraMap A k))
      (normalModelSection_over p σ hσ (Spec.algebraMap A k)) (Spec.algebraMap k F))
    (normalModelSection pR σR hσR (Spec.algebraMap R F))
    (normalGenericFibreIso_normalModelSection p σ hσ (Spec.algebraMap A R)
      (Spec.algebraMap A k) (Spec.algebraMap k F) (Spec.algebraMap R F) ht) z
  let hn := normalizedFamilyMap p (Spec.algebraMap A R) (Spec.algebraMap A B)
    (Spec.algebraMap B S) (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (SeparableBaseSquare.spec_square A B k F E a)
  Module.Finite A R ∧ IsFinite (Spec.algebraMap A R) ∧
    Module.Finite B S ∧ IsNoetherianRing S ∧ IsIntegrallyClosed S ∧
    IsFinite (Spec.algebraMap B S) ∧
    WholeMarkedOpenClassZero R S F pR σR hσR ZR zR hn M degree c

omit [Algebra A K] [Algebra k K] [IsScalarTower A B K] [IsScalarTower A k K]
  [IsScalarTower k K E] in
/-- Transport the unchanged selected generic class and its two original
projection laws, then extend the same marked cover over the whole source. -/
theorem normalWholeCoefficientOpen_of_generic_zero
    [QuasiCompact p] [QuasiSeparated p] [Smooth p] [GeometricallyConnected p]
    (Z : FiniteEtale (pullback (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F)))
    [IsGalois Z]
    (z : Fiber (normalModelSection (pullback.snd p (Spec.algebraMap A k))
      (normalModelSection p σ hσ (Spec.algebraMap A k))
      (normalModelSection_over p σ hσ (Spec.algebraMap A k)) (Spec.algebraMap k F)) Z)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap A B)))]
    (M : AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap A B)))
    (degree : ℕ) (c : Sheaf.H.{eX} M degree)
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A)) (hcard : Nat.card (Aut Z) ∣ N)
    (h0 : pullback (pullback.snd (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F))
      (Spec.map (CommRingCat.ofHom a.toRingHom)) ⟶ (pullback p (Spec.algebraMap A B)))
    (h0X : h0 ≫ pullback.fst p (Spec.algebraMap A B) =
      pullback.fst (pullback.snd (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)) ≫
        pullback.fst (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F) ≫
          pullback.fst p (Spec.algebraMap A k))
    (h0B : h0 ≫ pullback.snd p (Spec.algebraMap A B) =
      pullback.snd (pullback.snd (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)) ≫ Spec.algebraMap B E)
    (hc : cohomologyPullback.{u, eX, u + 2}
      (((baseChange (pullback.fst
        (pullback.snd (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)))).obj Z).obj.hom ≫ h0)
      M degree c = 0) :
    LiteralNormalWholeCoefficientOpen A B k K F E a p σ hσ Z z M degree c := by
  let R := integralClosure A F
  let S := integralClosure B E
  have hR := SeparableBaseSquare.normal_finite_model A k F
  have hS := SeparableBaseSquare.normal_finite_model B K E
  let : IsNoetherianRing R := hR.2.1
  let : IsIntegrallyClosed R := hR.2.2.1
  let : IsFractionRing R F := hR.2.2.2.1
  let : IsFractionRing S E := hS.2.2.2.1
  let φ := SeparableBaseSquare.closureMap A B k F E a
  let : Algebra R S := φ.toRingHom.toAlgebra
  let : Algebra R E := (a.toRingHom.comp (algebraMap R F)).toAlgebra
  let : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  let aR : F →ₐ[R] E := { a.toRingHom with commutes' := fun _ => rfl }
  let pR := pullback.snd p (Spec.algebraMap A R)
  let σR := normalModelSection p σ hσ (Spec.algebraMap A R)
  let hσR := normalModelSection_over p σ hσ (Spec.algebraMap A R)
  have ht : Spec.algebraMap R F ≫ Spec.algebraMap A R =
      Spec.algebraMap k F ≫ Spec.algebraMap A k := by
    simp only [Spec.algebraMap, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      ((IsScalarTower.algebraMap_eq A R F).symm.trans
        (IsScalarTower.algebraMap_eq A k F)))
  let i := normalGenericFibreIso p (Spec.algebraMap A k) (Spec.algebraMap A R)
    (Spec.algebraMap k F) (Spec.algebraMap R F) ht
  let ZR := (baseChange i.hom).obj Z
  let zR := normalGenericCoverPoint i Z (normalModelSection (pullback.snd p (Spec.algebraMap A k))
      (normalModelSection p σ hσ (Spec.algebraMap A k))
      (normalModelSection_over p σ hσ (Spec.algebraMap A k)) (Spec.algebraMap k F))
    (normalModelSection pR σR hσR (Spec.algebraMap R F))
    (normalGenericFibreIso_normalModelSection p σ hσ (Spec.algebraMap A R)
      (Spec.algebraMap A k) (Spec.algebraMap k F) (Spec.algebraMap R F) ht) z
  let hn := normalizedFamilyMap p (Spec.algebraMap A R) (Spec.algebraMap A B)
    (Spec.algebraMap B S) (Spec.map (CommRingCat.ofHom φ.toRingHom))
    (SeparableBaseSquare.spec_square A B k F E a)
  let f0 := pullback.snd (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F)
  let fR := pullback.snd pR (Spec.algebraMap R F)
  let g := Spec.map (CommRingCat.ofHom a.toRingHom)
  have hiF : i.hom ≫ f0 = fR := normalGenericFibreIso_field ..
  let v := pullback.map fR g f0 g i.hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using hiF.symm) (by simp)
  let C0 := (baseChange (pullback.fst f0 g)).obj Z
  let CR := (baseChange (pullback.fst fR g)).obj ZR
  have hvX : v ≫ pullback.fst f0 g = pullback.fst fR g ≫ i.hom := pullback.lift_fst ..
  have hvE : v ≫ pullback.snd f0 g = pullback.snd fR g := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  let vC : CR.obj.left ⟶ C0.obj.left :=
    pullback.lift (pullback.fst ZR.obj.hom (pullback.fst fR g) ≫ pullback.fst Z.obj.hom i.hom)
      (CR.obj.hom ≫ v) (by
        have hZ := pullback.condition (f := Z.obj.hom) («g» := i.hom)
        have hR := pullback.condition (f := ZR.obj.hom) («g» := pullback.fst fR g)
        exact (Category.assoc ..).trans
          ((congrArg (fun m => pullback.fst ZR.obj.hom (pullback.fst fR g) ≫ m) hZ).trans
            ((Category.assoc ..).symm.trans
              ((congrArg (fun m => m ≫ i.hom) hR).trans
                ((Category.assoc ..).trans
                  (congrArg (fun m => CR.obj.hom ≫ m) hvX.symm))))))
  have hvC : vC ≫ C0.obj.hom = CR.obj.hom ≫ v := pullback.lift_snd ..
  have hGfst : genericCoefficientFamilyMap R S F E aR pR ≫
      pullback.fst pR (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      pullback.fst fR g ≫ pullback.fst pR (Spec.algebraMap R F) := pullback.lift_fst ..
  have hGsnd : genericCoefficientFamilyMap R S F E aR pR ≫
      pullback.snd pR (Spec.map (CommRingCat.ofHom φ.toRingHom)) =
      pullback.snd fR g ≫ Spec.algebraMap S E := pullback.lift_snd ..
  have hnX : hn ≫ pullback.fst p (Spec.algebraMap A B) =
      pullback.fst pR (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
        pullback.fst p (Spec.algebraMap A R) := pullback.lift_fst ..
  have hnB : hn ≫ pullback.snd p (Spec.algebraMap A B) =
      pullback.snd pR (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
        Spec.algebraMap B S := pullback.lift_snd ..
  have hfamily : v ≫ h0 = genericCoefficientFamilyMap R S F E aR pR ≫ hn := by
    apply pullback.hom_ext
    · have hiX := normalGenericFibreIso_source p (Spec.algebraMap A k)
        (Spec.algebraMap A R) (Spec.algebraMap k F) (Spec.algebraMap R F) ht
      calc
        _ = v ≫ pullback.fst f0 g ≫
          pullback.fst (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F) ≫
            pullback.fst p (Spec.algebraMap A k) := by
          simpa only [Category.assoc] using congrArg (fun m => v ≫ m) h0X
        _ = pullback.fst fR g ≫ i.hom ≫
          pullback.fst (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F) ≫
            pullback.fst p (Spec.algebraMap A k) := by
          simpa only [Category.assoc] using congrArg (fun m => m ≫
            pullback.fst (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F) ≫
          pullback.fst p (Spec.algebraMap A k)) hvX
        _ = pullback.fst fR g ≫ pullback.fst pR (Spec.algebraMap R F) ≫
            pullback.fst p (Spec.algebraMap A R) := congrArg (fun m => pullback.fst fR g ≫ m) hiX
        _ = _ := by
          simpa only [Category.assoc] using
            ((congrArg (fun m => genericCoefficientFamilyMap R S F E aR pR ≫ m) hnX).trans
              (by
                simpa only [Category.assoc] using congrArg
                  (fun m => m ≫ pullback.fst p (Spec.algebraMap A R)) hGfst)).symm
    · have hSE : Spec.algebraMap S E ≫ Spec.algebraMap B S = Spec.algebraMap B E := by
        simp only [Spec.algebraMap, ← Spec.map_comp]
        exact congrArg Spec.map (CommRingCat.hom_ext (IsScalarTower.algebraMap_eq B S E).symm)
      calc
        _ = v ≫ pullback.snd f0 g ≫ Spec.algebraMap B E := by
          simpa only [Category.assoc] using congrArg (fun m => v ≫ m) h0B
        _ = pullback.snd fR g ≫ Spec.algebraMap B E := by
          simpa only [Category.assoc] using congrArg (fun m => m ≫ Spec.algebraMap B E) hvE
        _ = pullback.snd fR g ≫ Spec.algebraMap S E ≫ Spec.algebraMap B S :=
          congrArg (fun m => pullback.snd fR g ≫ m) hSE.symm
        _ = _ := by
          simpa only [Category.assoc] using
            ((congrArg (fun m => genericCoefficientFamilyMap R S F E aR pR ≫ m) hnB).trans
              (by
                simpa only [Category.assoc] using congrArg
                  (fun m => m ≫ Spec.algebraMap B S) hGsnd)).symm
  have hcover : vC ≫ (C0.obj.hom ≫ h0) =
      CR.obj.hom ≫ genericCoefficientFamilyMap R S F E aR pR ≫ hn :=
    (Category.assoc ..).symm.trans ((congrArg (fun m => m ≫ h0) hvC).trans
      ((Category.assoc ..).trans (congrArg (fun m => CR.obj.hom ≫ m) hfamily)))
  have hcR : cohomologyPullback.{u, eX, u + 2}
      (CR.obj.hom ≫ genericCoefficientFamilyMap R S F E aR pR ≫ hn) M degree c = 0 := by
    exact original_class_zero_of_map_law vC (C0.obj.hom ≫ h0) _ hcover M degree c hc
  let : ConnectedSpace
      (pullback (pullback.snd p (Spec.algebraMap A k)) (Spec.algebraMap k F) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton f0
  let : ConnectedSpace Z.obj.left := Connectedness.connectedSpace_of_categoricalConnected Z
  let : ConnectedSpace ZR.obj.left :=
    (asIso (pullback.fst Z.obj.hom i.hom)).inv.homeomorph.connectedSpace_iff.mp inferInstance
  let : IsGalois ZR := baseChange_isGalois_of_connected i.hom Z
  have hcardR : Nat.card (Aut ZR) ∣ N :=
    (baseChange_card_aut_of_connected i.hom Z) ▸ hcard
  let : CompactSpace (pullback p (Spec.algebraMap A R) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace pR
  let : QuasiSeparatedSpace (pullback p (Spec.algebraMap A R) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated pR
  have hunitR : IsUnit (N : R) := by
    simpa only [map_natCast] using hunit.map (algebraMap A R)
  have hmarked := whole_marked_open_class_zero R S F pR σR hσR ZR zR hn
    M degree c E aR N hN hunitR hcardR hcR
  exact ⟨hR.1, hR.2.2.2.2, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.2, hmarked⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
