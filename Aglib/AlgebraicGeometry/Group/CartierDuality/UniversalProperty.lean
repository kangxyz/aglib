/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.Affine.ScalarExtension
public import Aglib.AlgebraicGeometry.Group.CartierDuality.AffineCharacters
public import Aglib.AlgebraicGeometry.Group.CartierDuality.Coordinate
public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnits.Naturality
public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange
public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.HomCongr

/-!
# Characters of the original finite commutative group scheme

The chosen finite dual represents characters of the original native group
pullbacks. Coefficient algebras are arbitrary commutative algebras over the
field; no invertibility of the group order is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped TensorProduct Module.Dual.FiniteDual

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

open AlgebraicGeometry.Scheme.OverField (FScheme Base)

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]
  (R : Type u) [CommRing R] [Algebra k R]

/-- The original group pullback has the native scalar coordinate Hopf algebra. -/
def coordinateScalarExtensionIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp.obj G ≅
      (hopfSpec (CommRingCat.of R)).obj
        (op (CommHopfAlgCat.of R (R ⊗[k] coordinateHopf G))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))).mapGrp.mapIso
      (coordinateSpecIso G).symm ≪≫
    hopfSpecScalarExtensionIso k R (coordinateHopf G)

omit [IsCommMonObj G.X] in
/-- The inverse coordinate comparison preserves the original group projection. -/
theorem coordinateScalarExtensionIso_inv_fst :
    (coordinateScalarExtensionIso G R).inv.hom.hom.left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom (Spec.algebraMap k R) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : coordinateHopf G →ₐ[k]
          R ⊗[k] coordinateHopf G).toRingHom) ≫ (coordinateSpecIso G).hom.hom.hom.left := by
  have hm := BaseChange.groupSchemeBaseChange_map_left_fst
    (Spec.algebraMap k R) (coordinateSpecIso G).hom
  have hs := hopfSpecScalarExtensionIso_inv_fst k R (coordinateHopf G)
  dsimp only [BaseChange.groupSchemeBaseChange, specGroup, Functor.mapGrp_obj_X,
    Over.pullback_obj_left, Over.pullback_obj_hom] at hm
  have h1 := congrArg
    (fun q => (hopfSpecScalarExtensionIso k R (coordinateHopf G)).inv.hom.hom.left ≫ q) hm
  have h2 := congrArg (fun q => q ≫ (coordinateSpecIso G).hom.hom.hom.left) hs
  have hfinal := h1.trans h2
  simp only [coordinateScalarExtensionIso] at ⊢
  exact hfinal

omit [IsCommMonObj G.X] in
/-- The inverse coordinate comparison preserves the original coefficient projection. -/
theorem coordinateScalarExtensionIso_inv_snd :
    (coordinateScalarExtensionIso G R).inv.hom.hom.left ≫
        CategoryTheory.Limits.pullback.snd G.X.hom (Spec.algebraMap k R) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] coordinateHopf G))) := by
  have hm := BaseChange.groupSchemeBaseChange_map_left_snd
    (Spec.algebraMap k R) (coordinateSpecIso G).hom
  have hs := hopfSpecScalarExtensionIso_inv_snd k R (coordinateHopf G)
  dsimp only [BaseChange.groupSchemeBaseChange, specGroup, Functor.mapGrp_obj_X,
    Over.pullback_obj_left, Over.pullback_obj_hom] at hm
  have h1 := congrArg
    (fun q => (hopfSpecScalarExtensionIso k R (coordinateHopf G)).inv.hom.hom.left ≫ q) hm
  have hfinal := h1.trans hs
  simp only [coordinateScalarExtensionIso] at ⊢
  exact hfinal

/-- Affine points of the chosen Cartier dual are its original algebra points. -/
def affineDualPointEquiv :
    (Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) ≃
      (Dual k (coordinateHopf G) →ₐ[k] R) where
  toFun p := Spec.homEquivAlgHom ⟨p.left, Over.w p⟩
  invFun f := Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.algebraMap k (Dual k (coordinateHopf G)) = Spec.algebraMap k R
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.commutes r)
  left_inv p := by
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨p.left, Over.w p⟩)
  right_inv f := Spec.homEquivAlgHom.apply_symm_apply f

/-- The inverse affine point map keeps the original Spec arrow. -/
theorem affineDualPointEquiv_symm_left (f : Dual k (coordinateHopf G) →ₐ[k] R) :
    ((affineDualPointEquiv G R).symm f).left =
      Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

/-- The algebra point has the original whole scheme map as its native Spec. -/
theorem affineDualPointEquiv_left
    (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    Spec.map (CommRingCat.ofHom (affineDualPointEquiv G R p).toRingHom) = p.left :=
  congrArg Over.Hom.left ((affineDualPointEquiv G R).symm_apply_apply p)

/-- The inverse point construction is natural in all coefficient-algebra maps. -/
theorem affineDualPointEquiv_symm_comp {S : Type u} [CommRing S] [Algebra k S]
    (f : Dual k (coordinateHopf G) →ₐ[k] R) (g : R →ₐ[k] S) :
    (affineDualPointEquiv G S).symm (g.comp f) =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom g).op ≫
        (affineDualPointEquiv G R).symm f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp]
  rfl

/-- The algebra point of the identity point is the literal identity algebra map. -/
theorem affineDualPointEquiv_id :
    affineDualPointEquiv G (Dual k (coordinateHopf G)) (𝟙 (dualGroup G).X) =
      AlgHom.id k (Dual k (coordinateHopf G)) := by
  apply AlgHom.coe_ringHom_injective
  change (Spec.preimage (𝟙 (Spec (CommRingCat.of (Dual k (coordinateHopf G)))))).hom = _
  rw [Spec.preimage_id]
  rfl

/-- The chosen dual represents characters of the original group on every affine test. -/
def affineCharacterEquiv :
    (Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) ≃
      ((Over.pullback (Spec.algebraMap k R)).mapGrp.obj G ⟶
        MultiplicativeGroup.groupScheme (Spec (CommRingCat.of R))) :=
  (affineDualPointEquiv G R).trans
    ((scalarCharacterEquiv (coordinateHopf G) R).trans
      (Iso.homCongr (coordinateScalarExtensionIso G R).symm (Iso.refl _)))

/-- The represented character retains the original coordinate comparison and scalar character. -/
theorem affineCharacterEquiv_apply
    (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    affineCharacterEquiv G R p =
      (coordinateScalarExtensionIso G R).hom ≫
        scalarCharacterEquiv (coordinateHopf G) R (affineDualPointEquiv G R p) := by
  change (coordinateScalarExtensionIso G R).hom ≫
      scalarCharacterEquiv (coordinateHopf G) R (affineDualPointEquiv G R p) ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- Passing to the selected scalar coordinates recovers the original scalar character. -/
theorem affineCharacterEquiv_coordinates
    (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    (coordinateScalarExtensionIso G R).inv ≫ affineCharacterEquiv G R p =
      scalarCharacterEquiv (coordinateHopf G) R (affineDualPointEquiv G R p) := by
  rw [affineCharacterEquiv_apply, Iso.inv_hom_id_assoc]

/-- The whole affine character unit is the pullback of the original coevaluation unit. -/
theorem affineCharacterEquiv_coevaluation
    (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    specUnitsEquiv (CommAlgCat.of R (R ⊗[k] coordinateHopf G))
        ((coordinateScalarExtensionIso G R).inv ≫ affineCharacterEquiv G R p).hom.hom =
      Units.map (Module.Dual.characterTensorHom k (coordinateHopf G) R
        (affineDualPointEquiv G R p)).toMonoidHom
          (HopfAlgebra.coevaluationUnit k (coordinateHopf G)) := by
  rw [affineCharacterEquiv_coordinates]
  exact scalarCharacterEquiv_coevaluation (coordinateHopf G) R (affineDualPointEquiv G R p)

/-- The universal character is the character of the identity point of the chosen dual. -/
def universalCharacter :
    (Over.pullback (dualGroup G).X.hom).mapGrp.obj G ⟶
      MultiplicativeGroup.groupScheme (dualGroup G).X.left :=
  affineCharacterEquiv G (Dual k (coordinateHopf G)) (𝟙 (dualGroup G).X)

/-- The universal character is the scalar character of the literal identity algebra map. -/
theorem universalCharacter_coordinates :
    (coordinateScalarExtensionIso G (Dual k (coordinateHopf G))).inv ≫ universalCharacter G =
      scalarCharacterEquiv (coordinateHopf G) (Dual k (coordinateHopf G))
        (AlgHom.id k (Dual k (coordinateHopf G))) := by
  have h0 := affineCharacterEquiv_coordinates (k := k) G (Dual k (coordinateHopf G))
  have h := h0 (𝟙 (dualGroup G).X)
  have hid := affineDualPointEquiv_id (k := k) G
  exact h.trans (congrArg (scalarCharacterEquiv (coordinateHopf G)
    (Dual k (coordinateHopf G))) hid)

/-- The universal character unit is the original coevaluation unit with its two factors swapped. -/
theorem universalCharacter_coevaluation :
    specUnitsEquiv
        (CommAlgCat.of (Dual k (coordinateHopf G))
          (Dual k (coordinateHopf G) ⊗[k] coordinateHopf G))
        ((coordinateScalarExtensionIso G (Dual k (coordinateHopf G))).inv ≫
          universalCharacter G).hom.hom =
      Units.map (Algebra.TensorProduct.comm k (coordinateHopf G)
        (Dual k (coordinateHopf G))).toAlgHom.toMonoidHom
          (HopfAlgebra.coevaluationUnit k (coordinateHopf G)) := by
  rw [universalCharacter_coordinates, scalarCharacterEquiv_coevaluation]
  have h : Module.Dual.characterTensorHom k (coordinateHopf G)
      (Dual k (coordinateHopf G)) (AlgHom.id k (Dual k (coordinateHopf G))) =
      (Algebra.TensorProduct.comm k (coordinateHopf G) (Dual k (coordinateHopf G))).toAlgHom := by
    ext a <;> simp [Module.Dual.characterTensorHom]
  exact congrArg (fun f : coordinateHopf G ⊗[k] Dual k (coordinateHopf G) →ₐ[k]
      Dual k (coordinateHopf G) ⊗[k] coordinateHopf G =>
    Units.map f.toMonoidHom (HopfAlgebra.coevaluationUnit k (coordinateHopf G))) h

private theorem scalarCharacter_specUnitMap (A : CommHopfAlgCat.{u} k)
    [FiniteDimensional k A] (f : Dual k A →ₐ[k] R) :
    (scalarCharacterEquiv A R f).hom.hom =
      specUnitMap (CommAlgCat.of R (R ⊗[k] A))
        (Units.map (Module.Dual.characterTensorHom k A R f).toMonoidHom
          (HopfAlgebra.coevaluationUnit k A)) := by
  apply (specUnitsEquiv (CommAlgCat.of R (R ⊗[k] A))).injective
  rw [specUnitsEquiv_specUnitMap]
  exact scalarCharacterEquiv_coevaluation A R f

/-- The original universal character has the original represented coevaluation unit map. -/
theorem universalCharacter_specUnitMap :
    ((coordinateScalarExtensionIso G (Dual k (coordinateHopf G))).inv ≫
        universalCharacter G).hom.hom =
      specUnitMap
        (CommAlgCat.of (Dual k (coordinateHopf G))
          (Dual k (coordinateHopf G) ⊗[k] coordinateHopf G))
        (Units.map (Algebra.TensorProduct.comm k (coordinateHopf G)
          (Dual k (coordinateHopf G))).toAlgHom.toMonoidHom
            (HopfAlgebra.coevaluationUnit k (coordinateHopf G))) := by
  apply (specUnitsEquiv
    (CommAlgCat.of (Dual k (coordinateHopf G))
      (Dual k (coordinateHopf G) ⊗[k] coordinateHopf G))).injective
  rw [specUnitsEquiv_specUnitMap]
  exact universalCharacter_coevaluation (k := k) G

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- The original pullback map induced by a map of test schemes. -/
abbrev groupPullbackBaseMap {T U : FScheme k} (h : U ⟶ T) :=
  CategoryTheory.Limits.pullback.map G.X.hom U.hom G.X.hom T.hom
    (𝟙 _) h.left (𝟙 _) (by simp) ((Category.comp_id _).trans (Over.w h).symm)

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- The canonical base map retains the original group projection. -/
@[reassoc (attr := simp)]
theorem groupPullbackBaseMap_fst {T U : FScheme k} (h : U ⟶ T) :
    groupPullbackBaseMap G h ≫ CategoryTheory.Limits.pullback.fst G.X.hom T.hom =
      CategoryTheory.Limits.pullback.fst G.X.hom U.hom := by
  simp [groupPullbackBaseMap, CategoryTheory.Limits.pullback.map,
    CategoryTheory.Limits.pullback.lift_fst]

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- The canonical base map has exactly the prescribed test-scheme projection. -/
@[reassoc (attr := simp)]
theorem groupPullbackBaseMap_snd {T U : FScheme k} (h : U ⟶ T) :
    groupPullbackBaseMap G h ≫ CategoryTheory.Limits.pullback.snd G.X.hom T.hom =
      CategoryTheory.Limits.pullback.snd G.X.hom U.hom ≫ h.left := by
  simp [groupPullbackBaseMap, CategoryTheory.Limits.pullback.map,
    CategoryTheory.Limits.pullback.lift_snd]

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- The original pullback base map of an identity is identity. -/
@[simp]
theorem groupPullbackBaseMap_id (T : FScheme k) :
    groupPullbackBaseMap G (𝟙 T) = 𝟙 _ := by
  apply CategoryTheory.Limits.pullback.hom_ext <;> simp

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- The original pullback base maps compose in the original order. -/
theorem groupPullbackBaseMap_comp {T U V : FScheme k} (h : U ⟶ T) (g : V ⟶ U) :
    groupPullbackBaseMap G (g ≫ h) = groupPullbackBaseMap G g ≫ groupPullbackBaseMap G h := by
  apply CategoryTheory.Limits.pullback.hom_ext <;> simp [Category.assoc]

private theorem coordinate_inverse_base_square (k A D R : Type u)
    [CommRing k] [CommRing A] [CommRing D] [CommRing R]
    [Algebra k A] [Algebra k D] [Algebra k R]
    {X : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    (c : Spec (CommRingCat.of A) ⟶ X)
    (eR : Spec (CommRingCat.of (R ⊗[k] A)) ⟶
      CategoryTheory.Limits.pullback g (Spec.algebraMap k R))
    (eD : Spec (CommRingCat.of (D ⊗[k] A)) ⟶
      CategoryTheory.Limits.pullback g (Spec.algebraMap k D))
    (f : D →ₐ[k] R)
    (hfR : eR ≫ CategoryTheory.Limits.pullback.fst g (Spec.algebraMap k R) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A).toRingHom) ≫ c)
    (hfD : eD ≫ CategoryTheory.Limits.pullback.fst g (Spec.algebraMap k D) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] D ⊗[k] A).toRingHom) ≫ c)
    (hsR : eR ≫ CategoryTheory.Limits.pullback.snd g (Spec.algebraMap k R) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] A))))
    (hsD : eD ≫ CategoryTheory.Limits.pullback.snd g (Spec.algebraMap k D) =
      Spec.map (CommRingCat.ofHom (algebraMap D (D ⊗[k] A)))) :
    eR ≫ CategoryTheory.Limits.pullback.map g (Spec.algebraMap k R) g
        (Spec.algebraMap k D) (𝟙 _) (Spec.map (CommRingCat.ofHom f.toRingHom)) (𝟙 _)
        (by simp) (by
          change Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫ 𝟙 _ =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (algebraMap k D))
          rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 1
          ext r
          exact (f.commutes r).symm) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map f (AlgHom.id k A)).toRingHom) ≫ eD := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [CategoryTheory.Limits.pullback.map, Category.assoc,
      CategoryTheory.Limits.pullback.lift_fst, Category.comp_id]
    rw [hfR, hfD, ← Category.assoc]
    congr 1
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp
  · simp only [CategoryTheory.Limits.pullback.map, Category.assoc,
      CategoryTheory.Limits.pullback.lift_snd]
    rw [← Category.assoc, hsR, hsD]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2

/-- The original scalar coordinate comparison is natural at every affine dual point. -/
theorem coordinateScalarExtensionIso_inv_point_naturality
    (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    (coordinateScalarExtensionIso G R).inv.hom.hom.left ≫ groupPullbackBaseMap G p =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (affineDualPointEquiv G R p)
            (AlgHom.id k (coordinateHopf G))).toRingHom) ≫
        (coordinateScalarExtensionIso G (Dual k (coordinateHopf G))).inv.hom.hom.left := by
  obtain ⟨f, rfl⟩ := (affineDualPointEquiv G R).symm.surjective p
  simp only [Equiv.apply_symm_apply]
  have h0 := coordinate_inverse_base_square k (coordinateHopf G)
    (Dual k (coordinateHopf G)) R (X := G.X.left)
  have h := h0 G.X.hom (coordinateSpecIso G).hom.hom.hom.left
    (coordinateScalarExtensionIso G R).inv.hom.hom.left
    (coordinateScalarExtensionIso G (Dual k (coordinateHopf G))).inv.hom.hom.left f
    (coordinateScalarExtensionIso_inv_fst (k := k) G R)
    (coordinateScalarExtensionIso_inv_fst (k := k) G (Dual k (coordinateHopf G)))
    (coordinateScalarExtensionIso_inv_snd (k := k) G R)
    (coordinateScalarExtensionIso_inv_snd (k := k) G (Dual k (coordinateHopf G)))
  exact h

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
private theorem pullbackGroupCongr_fst {S : AlgebraicGeometry.Scheme.{u}}
    {f g : S ⟶ Base k} (e : f = g) :
    ((BaseChange.groupSchemeBaseChangeCongr e).hom.app G).hom.hom.left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom g =
      CategoryTheory.Limits.pullback.fst G.X.hom f := by
  cases e
  exact Category.id_comp _

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
private theorem pullbackGroupCongr_snd {S : AlgebraicGeometry.Scheme.{u}}
    {f g : S ⟶ Base k} (e : f = g) :
    ((BaseChange.groupSchemeBaseChangeCongr e).hom.app G).hom.hom.left ≫
        CategoryTheory.Limits.pullback.snd G.X.hom g =
      CategoryTheory.Limits.pullback.snd G.X.hom f := by
  cases e
  exact Category.id_comp _

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictCharacter_source {T U : FScheme k} (h : U ⟶ T) :
    (((BaseChange.groupSchemeBaseChangeCongr (Over.w h).symm).hom.app G) ≫
        (BaseChange.groupSchemeBaseChangeComp h.left T.hom).hom.app G).hom.hom.left ≫
        CategoryTheory.Limits.pullback.fst
          ((Over.pullback T.hom).mapGrp.obj G).X.hom h.left =
      groupPullbackBaseMap G h := by
  have hf := BaseChange.groupSchemeBaseChangeComp_hom_left_fst_fst h.left T.hom G
  have hs := BaseChange.groupSchemeBaseChangeComp_hom_left_fst_snd h.left T.hom G
  dsimp only [BaseChange.groupSchemeBaseChange, Functor.comp_obj,
    Functor.mapGrp_obj_X, Over.pullback_obj_hom, Over.pullback_obj_left] at hf hs ⊢
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
    rw [hf]
    rw [pullbackGroupCongr_fst]
    simp
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
    rw [hs]
    rw [← Category.assoc, pullbackGroupCongr_snd]
    simp

private theorem compose_coordinate_laws {C : Type*} [Category C]
    {X Y Z W : C} (q : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (u : Y ⟶ W) (v : Z ⟶ W) (hu : u = p ≫ v) (hs : q ≫ p = r) :
    q ≫ u = r ≫ v := by
  rw [hu, ← Category.assoc, hs]

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- Character restriction uses the original group pullback and the native Gm base-change map. -/
def restrictCharacter {T U : FScheme k} (h : U ⟶ T)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶
      MultiplicativeGroup.groupScheme T.left) :
    (Over.pullback U.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme U.left :=
  (BaseChange.groupSchemeBaseChangeCongr (Over.w h).symm).hom.app G ≫
    (BaseChange.groupSchemeBaseChangeComp h.left T.hom).hom.app G ≫
    (Over.pullback h.left).mapGrp.map c ≫
    (MultiplicativeBaseChange.unitsBaseChangeIso h.left).hom

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction keeps the original Laurent-coordinate pullback along the native base map. -/
theorem restrictCharacter_coordinates {T U : FScheme k} (h : U ⟶ T)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶
      MultiplicativeGroup.groupScheme T.left) :
    (restrictCharacter G h c).hom.hom.left ≫ CategoryTheory.Limits.prod.snd =
      groupPullbackBaseMap G h ≫
        c.hom.hom.left ≫ CategoryTheory.Limits.prod.snd := by
  have hm := BaseChange.groupSchemeBaseChange_map_left_fst h.left c
  have hs := restrictCharacter_source (k := k) G h
  have hu := MultiplicativeBaseChange.unitsBaseChangeIso_coordinate h.left
  dsimp only [BaseChange.groupSchemeBaseChange, Functor.comp_obj,
    Functor.mapGrp_obj_X, Over.pullback_obj_hom, Over.pullback_obj_left,
    MultiplicativeGroup.groupScheme] at hm hs
  have huc := congrArg
    (fun q => ((Over.pullback h.left).mapGrp.map c).hom.hom.left ≫ q) hu
  have hmc := congrArg (fun q => q ≫ CategoryTheory.Limits.prod.snd) hm
  simp only [Category.assoc] at huc hmc
  have hunit := huc.trans hmc
  have hfinal := compose_coordinate_laws _ _ _ _ _ hunit hs
  dsimp only [restrictCharacter]
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc] at hfinal ⊢
  exact hfinal

private theorem gm_groupMap_ext {S : AlgebraicGeometry.Scheme.{u}} {H : Grp (Over S)}
    {c d : H ⟶ MultiplicativeGroup.groupScheme S}
    (h : c.hom.hom.left ≫ CategoryTheory.Limits.prod.snd =
      d.hom.hom.left ≫ CategoryTheory.Limits.prod.snd) : c = d := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply CategoryTheory.Limits.prod.hom_ext
  · exact (Over.w c.hom.hom).trans (Over.w d.hom.hom).symm
  · exact h

private theorem character_compare_of_coordinates {S : AlgebraicGeometry.Scheme.{u}}
    {H K : Grp (Over S)} (e : H ≅ K)
    (c : H ⟶ MultiplicativeGroup.groupScheme S)
    (d : K ⟶ MultiplicativeGroup.groupScheme S)
    (h : e.inv.hom.hom.left ≫ c.hom.hom.left ≫ CategoryTheory.Limits.prod.snd =
      d.hom.hom.left ≫ CategoryTheory.Limits.prod.snd) : c = e.hom ≫ d := by
  apply (Iso.inv_comp_eq e).mp
  apply gm_groupMap_ext
  change (e.inv.hom.hom.left ≫ c.hom.hom.left) ≫ CategoryTheory.Limits.prod.snd =
    d.hom.hom.left ≫ CategoryTheory.Limits.prod.snd
  exact (Category.assoc _ _ _).trans h

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
private theorem character_ext {T : FScheme k}
    {c d : (Over.pullback T.hom).mapGrp.obj G ⟶
      MultiplicativeGroup.groupScheme T.left}
    (h : c.hom.hom.left ≫ CategoryTheory.Limits.prod.snd =
      d.hom.hom.left ≫ CategoryTheory.Limits.prod.snd) : c = d := by
  exact gm_groupMap_ext h

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- Restricting a character along the original identity changes nothing. -/
theorem restrictCharacter_id (T : FScheme k)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶
      MultiplicativeGroup.groupScheme T.left) :
    restrictCharacter G (𝟙 T) c = c := by
  have h0 := restrictCharacter_coordinates (k := k) G (𝟙 T) c
  rw [groupPullbackBaseMap_id, Category.id_comp] at h0
  exact character_ext G h0

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
/-- Character restriction is compatible with the original composition of test maps. -/
theorem restrictCharacter_comp {T U V : FScheme k} (h : U ⟶ T) (g : V ⟶ U)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶
      MultiplicativeGroup.groupScheme T.left) :
    restrictCharacter G (g ≫ h) c = restrictCharacter G g (restrictCharacter G h c) := by
  have hl := restrictCharacter_coordinates (k := k) G (g ≫ h) c
  have ho := restrictCharacter_coordinates (k := k) G g (restrictCharacter G h c)
  have hi := restrictCharacter_coordinates (k := k) G h c
  have hc := compose_coordinate_laws _ _ _ _ _ hi
    (groupPullbackBaseMap_comp (k := k) G h g).symm
  exact character_ext G (hl.trans (ho.trans hc).symm)

/-- Every original test-scheme point of the chosen dual gives an actual group character. -/
def characterOfPoint (T : FScheme k) (p : T ⟶ (dualGroup G).X) :
    (Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left :=
  restrictCharacter G p (universalCharacter G)

/-- The original character associated to a point is natural on arbitrary test schemes. -/
theorem characterOfPoint_naturality {T U : FScheme k} (h : U ⟶ T)
    (p : T ⟶ (dualGroup G).X) :
    characterOfPoint G U (h ≫ p) = restrictCharacter G h (characterOfPoint G T p) :=
  restrictCharacter_comp G p h (universalCharacter G)

/-- The arbitrary-test character retains the original Laurent coordinate of the universal one. -/
theorem characterOfPoint_coordinates (T : FScheme k) (p : T ⟶ (dualGroup G).X) :
    (characterOfPoint G T p).hom.hom.left ≫ CategoryTheory.Limits.prod.snd =
      groupPullbackBaseMap G p ≫ (universalCharacter G).hom.hom.left ≫
        CategoryTheory.Limits.prod.snd :=
  restrictCharacter_coordinates G p (universalCharacter G)

/-- On affine scalar coordinates, the arbitrary-test character is the original scalar character. -/
theorem characterOfPoint_affine_coordinates
    (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    (coordinateScalarExtensionIso G R).inv.hom.hom.left ≫
        (characterOfPoint G (Over.mk (Spec.algebraMap k R)) p).hom.hom.left ≫
        CategoryTheory.Limits.prod.snd =
      (scalarCharacterEquiv (coordinateHopf G) R (affineDualPointEquiv G R p)).hom.hom.left ≫
        CategoryTheory.Limits.prod.snd := by
  let f : Dual k (coordinateHopf G) →ₐ[k] R := affineDualPointEquiv G R p
  let coefficientMap : Dual k (coordinateHopf G) ⊗[k] coordinateHopf G →+*
      R ⊗[k] coordinateHopf G :=
    (Algebra.TensorProduct.map f (AlgHom.id k (coordinateHopf G))).toRingHom
  let u0 : (Dual k (coordinateHopf G) ⊗[k] coordinateHopf G)ˣ :=
    Units.map (Algebra.TensorProduct.comm k (coordinateHopf G)
      (Dual k (coordinateHopf G))).toAlgHom.toMonoidHom
        (HopfAlgebra.coevaluationUnit k (coordinateHopf G))
  have hc0 := characterOfPoint_coordinates (k := k) G (Over.mk (Spec.algebraMap k R)) p
  have hc := congrArg (fun q => (coordinateScalarExtensionIso G R).inv.hom.hom.left ≫ q) hc0
  have hsq0 := coordinateScalarExtensionIso_inv_point_naturality (k := k) G R p
  have hsq := congrArg
    (fun q => q ≫ (universalCharacter G).hom.hom.left ≫ CategoryTheory.Limits.prod.snd) hsq0
  have hu0 := universalCharacter_specUnitMap (k := k) G
  have huc := congrArg (fun q => q.left ≫ CategoryTheory.Limits.prod.snd) hu0
  have hup := congrArg (fun q => Spec.map (CommRingCat.ofHom coefficientMap) ≫ q) huc
  have hn0 := specUnitMap_laurent_naturality
    (CommAlgCat.of (Dual k (coordinateHopf G))
      (Dual k (coordinateHopf G) ⊗[k] coordinateHopf G))
    (CommAlgCat.of R (R ⊗[k] coordinateHopf G))
  have hn := hn0 coefficientMap u0
  have hsc0 := scalarCharacter_specUnitMap (k := k) (R := R) (coordinateHopf G) f
  have hsc := congrArg (fun q => q.left ≫ CategoryTheory.Limits.prod.snd) hsc0
  have hu : Units.map coefficientMap.toMonoidHom u0 =
      Units.map (Module.Dual.characterTensorHom k (coordinateHopf G) R f).toMonoidHom
        (HopfAlgebra.coevaluationUnit k (coordinateHopf G)) := by
    apply Units.ext
    rfl
  have hum := congrArg
    (fun u : (R ⊗[k] coordinateHopf G)ˣ =>
      (specUnitMap (CommAlgCat.of R (R ⊗[k] coordinateHopf G)) u).left ≫
        CategoryTheory.Limits.prod.snd) hu
  have hfinal := hc.trans (hsq.trans (hup.trans (hn.trans (hum.trans hsc.symm))))
  exact hfinal

/-- The original affine bijection is exactly restriction of the same universal character. -/
theorem characterOfPoint_affine
    (p : Over.mk (Spec.algebraMap k R) ⟶ (dualGroup G).X) :
    characterOfPoint G (Over.mk (Spec.algebraMap k R)) p = affineCharacterEquiv G R p := by
  have hp := characterOfPoint_affine_coordinates (k := k) G R p
  have hc := character_compare_of_coordinates (coordinateScalarExtensionIso G R)
    (characterOfPoint G (Over.mk (Spec.algebraMap k R)) p)
    (scalarCharacterEquiv (coordinateHopf G) R (affineDualPointEquiv G R p)) hp
  have ha := affineCharacterEquiv_apply (k := k) G R p
  exact hc.trans ha.symm

/-- The same universal character is bijective on every affine coefficient test. -/
theorem characterOfPoint_affine_bijective :
    Function.Bijective (characterOfPoint G (Over.mk (Spec.algebraMap k R))) := by
  have h := funext (characterOfPoint_affine (k := k) G R)
  rw [h]
  exact (affineCharacterEquiv G R).bijective

/-- Bijectivity of the same point-character map is preserved by an original test isomorphism. -/
theorem characterOfPoint_bijective_of_iso {T U : FScheme k} (e : T ≅ U)
    (hU : Function.Bijective (characterOfPoint G U)) :
    Function.Bijective (characterOfPoint G T) := by
  constructor
  · intro p q hpq
    have hp := characterOfPoint_naturality (k := k) G e.inv p
    have hq := characterOfPoint_naturality (k := k) G e.inv q
    have hr := congrArg (restrictCharacter G e.inv) hpq
    exact (cancel_epi e.inv).mp (hU.1 (hp.trans (hr.trans hq.symm)))
  · intro c
    obtain ⟨p, hp⟩ := hU.2 (restrictCharacter G e.inv c)
    refine ⟨e.hom ≫ p, ?_⟩
    have h1 := characterOfPoint_naturality (k := k) G e.hom p
    have h2 := congrArg (restrictCharacter G e.hom) hp
    have h3 := (restrictCharacter_comp (k := k) G e.inv e.hom c).symm
    have h4 : restrictCharacter G (e.hom ≫ e.inv) c = c := by
      rw [Iso.hom_inv_id, restrictCharacter_id]
    exact h1.trans (h2.trans (h3.trans h4))

/-- The original point-character map is bijective on every affine test scheme. -/
theorem characterOfPoint_bijective_of_isAffine (T : FScheme k) [IsAffine T.left] :
    Function.Bijective (characterOfPoint G T) := by
  let : T.left.Over (Base k) := OverClass.fromOver T
  let : Algebra k Γ(T.left, ⊤) := affineCoordinateAlgebra (CommRingCat.of k) T.left
  let e : T ≅ Over.mk (Spec.algebraMap k Γ(T.left, ⊤)) :=
    T.left.isoSpec.asOver (Base k)
  have h := characterOfPoint_affine_bijective (k := k) G Γ(T.left, ⊤)
  exact characterOfPoint_bijective_of_iso (k := k) G e h

private abbrev coverTest (T : FScheme k)
    (cover : AlgebraicGeometry.Scheme.OpenCover.{u} T.left) (i : cover.I₀) : FScheme k :=
  Over.mk (cover.f i ≫ T.hom)

private def coverTestMap (T : FScheme k)
    (cover : AlgebraicGeometry.Scheme.OpenCover.{u} T.left) (i : cover.I₀) :
    coverTest T cover i ⟶ T :=
  Over.homMk (cover.f i) (by rfl)

omit [IsFinite G.X.hom] [IsCommMonObj G.X] in
private theorem restrictCharacter_jointly_injective (T : FScheme k)
    (cover : AlgebraicGeometry.Scheme.OpenCover.{u} T.left)
    (c d : (Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left)
    (h : ∀ i, restrictCharacter G (coverTestMap T cover i) c =
      restrictCharacter G (coverTestMap T cover i) d) : c = d := by
  apply character_ext G
  apply (AlgebraicGeometry.Scheme.Pullback.openCoverOfRight cover G.X.hom T.hom).hom_ext
  intro i
  have hc := restrictCharacter_coordinates (k := k) G (coverTestMap T cover i) c
  have hd := restrictCharacter_coordinates (k := k) G (coverTestMap T cover i) d
  have he := congrArg
    (fun q => q.hom.hom.left ≫ CategoryTheory.Limits.prod.snd) (h i)
  have hfinal := hc.symm.trans (he.trans hd)
  change groupPullbackBaseMap G (coverTestMap T cover i) ≫ c.hom.hom.left ≫
      CategoryTheory.Limits.prod.snd =
    groupPullbackBaseMap G (coverTestMap T cover i) ≫ d.hom.hom.left ≫
      CategoryTheory.Limits.prod.snd
  exact hfinal

/-- The original point-character map is injective on every test scheme. -/
theorem characterOfPoint_injective (T : FScheme k) :
    Function.Injective (characterOfPoint G T) := by
  intro p q hc
  apply Over.OverMorphism.ext
  apply T.left.affineCover.hom_ext
  intro i
  let U : FScheme k := coverTest T T.left.affineCover i
  let j : U ⟶ T := coverTestMap T T.left.affineCover i
  let : IsAffine U.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have hp := characterOfPoint_naturality (k := k) G j p
  have hq := characterOfPoint_naturality (k := k) G j q
  have hr := congrArg (restrictCharacter G j) hc
  have hi := (characterOfPoint_bijective_of_isAffine (k := k) G U).1
  have he := hi (hp.trans (hr.trans hq.symm))
  exact congrArg Over.Hom.left he

/-- Every actual character on an arbitrary test scheme is represented by a point
of the chosen dual. -/
theorem characterOfPoint_surjective (T : FScheme k) :
    Function.Surjective (characterOfPoint G T) := by
  classical
  intro c
  let cover := T.left.affineCover
  have hlocal (i : cover.I₀) :
      ∃ p : coverTest T cover i ⟶ (dualGroup G).X,
        characterOfPoint G (coverTest T cover i) p =
          restrictCharacter G (coverTestMap T cover i) c := by
    let : IsAffine (coverTest T cover i).left :=
      inferInstanceAs (IsAffine (T.left.affineCover.X i))
    exact (characterOfPoint_bijective_of_isAffine (k := k) G (coverTest T cover i)).2 _
  let p (i : cover.I₀) : coverTest T cover i ⟶ (dualGroup G).X := (hlocal i).choose
  have hp (i : cover.I₀) : characterOfPoint G (coverTest T cover i) (p i) =
      restrictCharacter G (coverTestMap T cover i) c := (hlocal i).choose_spec
  have hcompat (i j : cover.I₀) :
      CategoryTheory.Limits.pullback.fst (cover.f i) (cover.f j) ≫ (p i).left =
        CategoryTheory.Limits.pullback.snd (cover.f i) (cover.f j) ≫ (p j).left := by
    let W : FScheme k := Over.mk
      (CategoryTheory.Limits.pullback.fst (cover.f i) (cover.f j) ≫ cover.f i ≫ T.hom)
    let a : W ⟶ coverTest T cover i :=
      Over.homMk (CategoryTheory.Limits.pullback.fst (cover.f i) (cover.f j)) (by rfl)
    let b : W ⟶ coverTest T cover j :=
      Over.homMk (CategoryTheory.Limits.pullback.snd (cover.f i) (cover.f j)) (by
        change CategoryTheory.Limits.pullback.snd (cover.f i) (cover.f j) ≫ cover.f j ≫ T.hom =
          CategoryTheory.Limits.pullback.fst (cover.f i) (cover.f j) ≫ cover.f i ≫ T.hom
        exact (CategoryTheory.Limits.pullback.condition_assoc
          (f := cover.f i) (g := cover.f j) T.hom).symm)
    have hbase : a ≫ coverTestMap T cover i = b ≫ coverTestMap T cover j := by
      apply Over.OverMorphism.ext
      exact CategoryTheory.Limits.pullback.condition
    have ha := characterOfPoint_naturality (k := k) G a (p i)
    have hb := characterOfPoint_naturality (k := k) G b (p j)
    have hai := congrArg (restrictCharacter G a) (hp i)
    have hbj := congrArg (restrictCharacter G b) (hp j)
    have hac := (restrictCharacter_comp (k := k) G (coverTestMap T cover i) a c).symm
    have hbc := (restrictCharacter_comp (k := k) G (coverTestMap T cover j) b c).symm
    have ht := congrArg (fun f : W ⟶ T => restrictCharacter G f c) hbase
    have hchars := ha.trans (hai.trans (hac.trans
      (ht.trans (hbc.symm.trans (hbj.symm.trans hb.symm)))))
    have hpoints := characterOfPoint_injective (k := k) G W hchars
    exact congrArg Over.Hom.left hpoints
  let f := cover.glueMorphisms (fun i => (p i).left) hcompat
  have hf : f ≫ (dualGroup G).X.hom = T.hom := by
    apply cover.hom_ext
    intro i
    rw [← Category.assoc]
    change (cover.f i ≫ cover.glueMorphisms (fun j => (p j).left) hcompat) ≫
      (dualGroup G).X.hom = cover.f i ≫ T.hom
    rw [cover.ι_glueMorphisms]
    exact (p i).w
  let q : T ⟶ (dualGroup G).X := Over.homMk f hf
  refine ⟨q, ?_⟩
  apply restrictCharacter_jointly_injective (k := k) G T cover
  intro i
  have hq : coverTestMap T cover i ≫ q = p i := by
    apply Over.OverMorphism.ext
    exact cover.ι_glueMorphisms (fun j => (p j).left) hcompat i
  have hn := characterOfPoint_naturality (k := k) G (coverTestMap T cover i) q
  have he := congrArg (characterOfPoint G (coverTest T cover i)) hq
  exact hn.symm.trans (he.trans (hp i))

/-- The chosen finite Cartier dual represents actual characters on every original test scheme. -/
def characterEquiv (T : FScheme k) :
    (T ⟶ (dualGroup G).X) ≃
      ((Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left) :=
  Equiv.ofBijective (characterOfPoint G T)
    ⟨characterOfPoint_injective G T, characterOfPoint_surjective G T⟩

/-- The representing bijection uses the same original character restriction map. -/
theorem characterEquiv_apply (T : FScheme k) (p : T ⟶ (dualGroup G).X) :
    characterEquiv G T p = characterOfPoint G T p := rfl

/-- Naturality of the full representing bijection on arbitrary test schemes. -/
theorem characterEquiv_naturality {T U : FScheme k} (h : U ⟶ T)
    (p : T ⟶ (dualGroup G).X) :
    characterEquiv G U (h ≫ p) = restrictCharacter G h (characterEquiv G T p) :=
  characterOfPoint_naturality G h p

/-- The inverse representing map is natural on arbitrary original tests. -/
theorem characterEquiv_symm_naturality {T U : FScheme k} (h : U ⟶ T)
    (c : (Over.pullback T.hom).mapGrp.obj G ⟶ MultiplicativeGroup.groupScheme T.left) :
    (characterEquiv G U).symm (restrictCharacter G h c) =
      h ≫ (characterEquiv G T).symm c := by
  apply characterOfPoint_injective (k := k) G U
  have hu := (characterEquiv G U).apply_symm_apply (restrictCharacter G h c)
  have ht := (characterEquiv G T).apply_symm_apply c
  have hn := characterOfPoint_naturality (k := k) G h ((characterEquiv G T).symm c)
  have hr := congrArg (restrictCharacter G h) ht
  exact hu.trans (hn.trans hr).symm

/-- The universal point of the same representing bijection is the original universal character. -/
theorem characterEquiv_universal :
    characterEquiv G (dualGroup G).X (𝟙 (dualGroup G).X) = universalCharacter G := by
  change restrictCharacter G (𝟙 (dualGroup G).X) (universalCharacter G) = _
  exact restrictCharacter_id (k := k) G (dualGroup G).X (universalCharacter G)

/-- Actual characters of the original group pullbacks, as a presheaf on the original tests. -/
def characterFunctor : (FScheme k)ᵒᵖ ⥤ Type u where
  obj T := (Over.pullback T.unop.hom).mapGrp.obj G ⟶
    MultiplicativeGroup.groupScheme T.unop.left
  map h := TypeCat.ofHom (restrictCharacter G h.unop)
  map_id T := by
    apply TypeCat.homEquiv.injective
    funext c
    exact restrictCharacter_id (k := k) G T.unop c
  map_comp h g := by
    apply TypeCat.homEquiv.injective
    funext c
    exact restrictCharacter_comp (k := k) G h.unop g.unop c

/-- The same native finite dual represents the actual character presheaf on every test. -/
def characterRepresentableBy :
    (characterFunctor G).RepresentableBy (dualGroup G).X where
  homEquiv := fun {T} => characterEquiv (k := k) G T
  homEquiv_comp {T U} h p := by
    change characterEquiv G T (h ≫ p) = restrictCharacter G h (characterEquiv G U p)
    exact characterEquiv_naturality (k := k) G h p

end AlgebraicGeometry.Scheme.Group.CartierDuality
