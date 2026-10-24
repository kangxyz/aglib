/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedBlowupCover
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Stalks

/-!
# The actual finite normal cover of a normalized ideal blowup

Normalize the literal generic map from the original field of Spec B to the
actual normalized J-blowup. The generic scalar action is the original field
map of Spec B to Spec A after the inverse of the original blowdown field map.
Finiteness and normality use the native finite-etale generic normalization.

Relative normalization's integral-factor universal map to the literal fibre
product constructs the original B-structure and its exact square. The exact
generic triangle proves birationality of that original B-map. The original
J-image ideal remains invertible with nonzero regular local frames after both
possibly nonflat normalizations. No map to a further proper model is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover

universe u

namespace Cover

variable {S T X : Scheme.{u}} [IsIntegral S] [IsIntegral T] [IsIntegral X]

/-- The inverse is that of the original birational function-field map. -/
def baseFieldIso (a : X ⟶ S) [IsDominant a]
    (ha : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap a))) :
    S.functionField ≅ X.functionField :=
  @asIso CommRingCat.{u} _ S.functionField X.functionField
    (CommRingCat.ofHom (Scheme.functionFieldMap a)) ha

variable (a : X ⟶ S) [IsDominant a]
  (ha : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap a)))
  (s : T ⟶ S) [IsDominant s]

/-- The field equivalence has the original blowdown field homomorphism. -/
@[simp] theorem baseFieldIso_hom :
    (baseFieldIso a ha).hom = CommRingCat.ofHom (Scheme.functionFieldMap a) := rfl

/-- The specified generic cover has the original field of T as its source.
Its scalar map is the original map for s after the inverse original map for a. -/
def genericCover : Spec T.functionField ⟶ Spec X.functionField :=
  Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap s)) ≫
    Spec.map (baseFieldIso a ha).inv

/-- The scalar action is literally the original extension after the inverse
of the original birational map, on the unchanged original field of T. -/
theorem genericCover_eq_specMap : genericCover a ha s =
    Spec.map ((baseFieldIso a ha).inv ≫ CommRingCat.ofHom (Scheme.functionFieldMap s)) :=
  (Spec.map_comp _ _).symm

instance genericCover_isAffineHom : IsAffineHom (genericCover a ha s) := by
  unfold genericCover
  infer_instance

instance genericCover_isSurjective : Surjective (genericCover a ha s) := by
  let : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  exact ⟨Function.surjective_to_subsingleton _⟩

/-- The original L-valued generic map to X. -/
def genericMap : Spec T.functionField ⟶ X :=
  genericCover a ha s ≫ X.fromSpecStalk (genericPoint X)

instance genericMap_isQuasiCompact : QuasiCompact (genericMap a ha s) := by
  unfold genericMap
  infer_instance

instance genericMap_isQuasiSeparated : QuasiSeparated (genericMap a ha s) := by
  unfold genericMap
  infer_instance

instance genericMap_isDominant : IsDominant (genericMap a ha s) := by
  unfold genericMap
  infer_instance

/-- The actual generic square follows from naturality of the original
function-field maps and cancellation of the original isomorphism. -/
@[reassoc] theorem genericMap_a :
    genericMap a ha s ≫ a = T.fromSpecStalk (genericPoint T) ≫ s := by
  unfold genericMap genericCover
  rw [Category.assoc, Category.assoc, Scheme.fromSpecStalk_genericPoint_naturality a]
  change Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap s)) ≫
    Spec.map (baseFieldIso a ha).inv ≫ Spec.map (baseFieldIso a ha).hom ≫
      S.fromSpecStalk (genericPoint S) = _
  rw [← Spec.map_comp_assoc (baseFieldIso a ha).hom (baseFieldIso a ha).inv,
    Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  exact (Scheme.fromSpecStalk_genericPoint_naturality s).symm

/-- Normalize this actual generic map, with the actual original field as source. -/
def normalization : Scheme.{u} := (genericMap a ha s).normalization

/-- The original finite-cover structural map. -/
def pi : normalization a ha s ⟶ X := (genericMap a ha s).fromNormalization

/-- The actual generic arrow into the relative normalization. -/
def eta : Spec T.functionField ⟶ normalization a ha s := (genericMap a ha s).toNormalization

instance normalization_isIntegral : IsIntegral (normalization a ha s) :=
  inferInstanceAs (IsIntegral (genericMap a ha s).normalization)

instance eta_isDominant : IsDominant (eta a ha s) :=
  inferInstanceAs (IsDominant (genericMap a ha s).toNormalization)

@[reassoc] theorem eta_pi : eta a ha s ≫ pi a ha s = genericMap a ha s :=
  Scheme.Hom.toNormalization_fromNormalization _

instance pi_isDominant : IsDominant (pi a ha s) := by
  let : IsDominant (eta a ha s ≫ pi a ha s) := by rw [eta_pi]; infer_instance
  exact IsDominant.of_comp (eta a ha s) (pi a ha s)

/-- Finiteness of the specified generic cover uses the original field map. -/
theorem genericCover_isFinite (hfin : (Scheme.functionFieldMap s).Finite) :
    IsFinite (genericCover a ha s) := by
  have hFinite : IsFinite (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap s))) :=
    (IsFinite.SpecMap_iff _).mpr hfin
  have hIsoFinite : IsFinite (Spec.map (baseFieldIso a ha).inv) := inferInstance
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.IsFinite.{u}) _ _ hFinite hIsoFinite

/-- Separability is used for the original scalar action before changing the
base field along its specified isomorphism. -/
theorem genericCover_etale (hfin : (Scheme.functionFieldMap s).Finite)
    (hsep : letI := Scheme.functionFieldMapAlgebra s
      Algebra.IsSeparable S.functionField T.functionField) :
    Etale (genericCover a ha s) := by
  let := Scheme.functionFieldMapAlgebra s
  let : Module.Finite S.functionField T.functionField := hfin
  let : Algebra.IsSeparable S.functionField T.functionField := hsep
  let : Algebra.FormallyEtale S.functionField T.functionField :=
    Algebra.FormallyEtale.of_isSeparable _ _
  let : Algebra.FinitePresentation S.functionField T.functionField :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale S.functionField T.functionField := ⟨inferInstance, inferInstance⟩
  have hEtale : Etale (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap s))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have hIsoEtale : AlgebraicGeometry.Etale (Spec.map (baseFieldIso a ha).inv) := inferInstance
  exact @AlgebraicGeometry.Etale.etale_comp _ _ _ _ _ hEtale hIsoEtale

/-- Finiteness is proved for the literal relative normalization in the same L. -/
theorem pi_isFinite [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hfin : (Scheme.functionFieldMap s).Finite)
    (hsep : letI := Scheme.functionFieldMapAlgebra s
      Algebra.IsSeparable S.functionField T.functionField) : IsFinite (pi a ha s) := by
  let : IsFinite (genericCover a ha s) := genericCover_isFinite a ha s hfin
  let : Etale (genericCover a ha s) := genericCover_etale a ha s hfin hsep
  let C : Scheme.FiniteEtale (Spec X.functionField) := Scheme.FiniteEtale.mk (genericCover a ha s)
  exact Scheme.FiniteEtale.GenericNormalization.instIsFinite X C

/-- Every actual relative-normalization stalk is normal. -/
theorem normalization_normalStalks [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hfin : (Scheme.functionFieldMap s).Finite)
    (hsep : letI := Scheme.functionFieldMapAlgebra s
      Algebra.IsSeparable S.functionField T.functionField) :
    NormalStalks (normalization a ha s) := by
  let : IsFinite (genericCover a ha s) := genericCover_isFinite a ha s hfin
  let : Etale (genericCover a ha s) := genericCover_etale a ha s hfin hsep
  let C : Scheme.FiniteEtale (Spec X.functionField) := Scheme.FiniteEtale.mk (genericCover a ha s)
  intro y
  exact (Scheme.FiniteEtale.GenericNormalization.stalk_normal_domain X C y).symm

/-- Local Noetherianity follows from the actual finite map. -/
theorem normalization_isLocallyNoetherian [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hfin : (Scheme.functionFieldMap s).Finite)
    (hsep : letI := Scheme.functionFieldMapAlgebra s
      Algebra.IsSeparable S.functionField T.functionField) :
    IsLocallyNoetherian (normalization a ha s) := by
  let : IsFinite (pi a ha s) := pi_isFinite a ha s hfin hsep
  exact LocallyOfFiniteType.isLocallyNoetherian (pi a ha s)

variable [IsFinite s]

/-- The original generic map lifts to the literal base fibre product. -/
def genericLift : Spec T.functionField ⟶ pullback a s :=
  pullback.lift (genericMap a ha s) (T.fromSpecStalk (genericPoint T)) (genericMap_a a ha s)

/-- Relative normalization's integral-factor universal map produces the
original map into the literal base fibre product. -/
def toPullback : normalization a ha s ⟶ pullback a s :=
  (genericMap a ha s).normalizationDesc (genericLift a ha s) (pullback.fst a s)
    (by exact (pullback.lift_fst _ _ _).symm)

@[reassoc] theorem toPullback_fst : toPullback a ha s ≫ pullback.fst a s = pi a ha s :=
  (genericMap a ha s).normalizationDesc_comp _ _ _

/-- The original B-structure is constructed from the integral-factor map. -/
def b : normalization a ha s ⟶ T := toPullback a ha s ≫ pullback.snd a s

/-- The literal square between original structural morphisms. -/
@[reassoc] theorem square : pi a ha s ≫ a = b a ha s ≫ s := by
  rw [← toPullback_fst a ha s]
  simp only [b, Category.assoc, pullback.condition]

/-- The original generic arrow to T is retained exactly. -/
@[reassoc] theorem eta_b :
    eta a ha s ≫ b a ha s = T.fromSpecStalk (genericPoint T) := by
  unfold b
  rw [← Category.assoc]
  change ((genericMap a ha s).toNormalization ≫
    (genericMap a ha s).normalizationDesc (genericLift a ha s) (pullback.fst a s) _) ≫ _ = _
  rw [Scheme.Hom.toNormalization_normalizationDesc]
  exact pullback.lift_snd _ _ _

instance b_isDominant : IsDominant (b a ha s) := by
  let : IsDominant (eta a ha s ≫ b a ha s) := by rw [eta_b]; infer_instance
  exact IsDominant.of_comp (eta a ha s) (b a ha s)

/-- The original b map is birational. Its field map is forced by the exact
generic triangle and the injective field map of the actual normalization arrow. -/
theorem b_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (b a ha s))) := by
  let γ := T.fromSpecStalk (genericPoint T)
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap γ)) :=
    Scheme.genericInclusion_fieldMap_isIso T
  have hcongr {c d : Spec T.functionField ⟶ T}
      [IsDominant c] [IsDominant d] (hcd : c = d) :
      Scheme.functionFieldMap c = Scheme.functionFieldMap d := by
    subst d
    rfl
  have hmap : (Scheme.functionFieldMap (eta a ha s)).comp
      (Scheme.functionFieldMap (b a ha s)) = Scheme.functionFieldMap γ :=
    (Scheme.functionFieldMap_comp (eta a ha s) (b a ha s)).symm.trans
      (hcongr (eta_b a ha s))
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(Scheme.functionFieldMap (b a ha s)).injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Scheme.functionFieldMap γ))).2
      (Scheme.functionFieldMap (eta a ha s) y)
  refine ⟨x, (Scheme.functionFieldMap (eta a ha s)).injective ?_⟩
  change ((Scheme.functionFieldMap (eta a ha s)).comp
    (Scheme.functionFieldMap (b a ha s))) x = _
  exact (RingHom.congr_fun hmap x).trans hx

/-- Properness of b follows from its actual square, proper a and finite pi. -/
theorem b_isProper [IsProper a] [IsFinite (pi a ha s)] : IsProper (b a ha s) := by
  let : IsProper (b a ha s ≫ s) := by rw [← square]; infer_instance
  exact IsProper.of_comp (b a ha s) s

end Cover

namespace FiniteBase

open AlgebraicGeometry.Scheme.Blowup

variable (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  (J : Ideal A) (hJ : J ≠ ⊥)
  (s : Spec (.of B) ⟶ Spec (.of A)) [IsDominant s] [IsFinite s]

/-- The actual relative normalization of the actual normalized J-blowup
in the original function field of Spec B. -/
def Y : Scheme.{u} :=
  Cover.normalization (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

/-- The original finite-cover map to the actual normalized J-blowup. -/
def pi : Y A B J hJ s ⟶ Base.normalization A J hJ :=
  Cover.pi (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

/-- The original B-structure constructed by relative normalization. -/
def b : Y A B J hJ s ⟶ Spec (.of B) :=
  Cover.b (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

/-- The original Spec L arrow into Y. -/
def eta : Spec (Spec (.of B)).functionField ⟶ Y A B J hJ s :=
  Cover.eta (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

instance Y_isIntegral : IsIntegral (Y A B J hJ s) :=
  inferInstanceAs (IsIntegral (Cover.normalization (Base.a A J hJ)
    (Base.a_fieldMap_isIso A J hJ) s))

instance pi_isDominant : IsDominant (pi A B J hJ s) :=
  inferInstanceAs (IsDominant (Cover.pi (Base.a A J hJ)
    (Base.a_fieldMap_isIso A J hJ) s))

instance b_isDominant : IsDominant (b A B J hJ s) :=
  inferInstanceAs (IsDominant (Cover.b (Base.a A J hJ)
    (Base.a_fieldMap_isIso A J hJ) s))

instance eta_isDominant : IsDominant (eta A B J hJ s) :=
  inferInstanceAs (IsDominant (Cover.eta (Base.a A J hJ)
    (Base.a_fieldMap_isIso A J hJ) s))

/-- The literal original square for this actual blowup construction. -/
@[reassoc] theorem square : pi A B J hJ s ≫ Base.a A J hJ = b A B J hJ s ≫ s :=
  Cover.square (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

/-- The exact original generic B-structure is retained. -/
@[reassoc] theorem eta_b :
    eta A B J hJ s ≫ b A B J hJ s =
      (Spec (.of B)).fromSpecStalk (genericPoint (Spec (.of B))) :=
  Cover.eta_b (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

/-- Birationality is on b's original function-field map. -/
theorem b_fieldMap_isIso :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (b A B J hJ s))) :=
  Cover.b_fieldMap_isIso (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

/-- The actual image of the original J-ideal on Y. -/
def imageIdeal : (Y A B J hJ s).IdealSheafData :=
  (Base.imageIdeal A J hJ).comap (pi A B J hJ s)

omit [IsFinite s] in
/-- The image ideal is computed by the literal composite to Spec A. -/
theorem imageIdeal_eq : imageIdeal A B J hJ s =
    (affineCenter A J).comap (pi A B J hJ s ≫ Base.a A J hJ) := by
  rw [imageIdeal, Base.imageIdeal_eq, Scheme.IdealSheafData.comap_comp]

/-- The same ideal is the pullback along the original B-structure. -/
theorem imageIdeal_eq_over_B : imageIdeal A B J hJ s =
    ((affineCenter A J).comap s).comap (b A B J hJ s) := by
  rw [imageIdeal_eq, square, Scheme.IdealSheafData.comap_comp]

omit [IsFinite s] in
/-- The original J-image is invertible after both possibly nonflat normalizations. -/
theorem imageIdeal_isLocallyRankOne :
    IsLocallyRankOne (Y A B J hJ s) (Hom.idealModule (imageIdeal A B J hJ s).subschemeι) :=
  NormalizedBlowupCover.imageIdeal_isLocallyRankOne (Base.imageIdeal A J hJ) (pi A B J hJ s)
    (Base.imageIdeal_generic_avoidance A J hJ) (Base.imageIdeal_isLocallyRankOne A J hJ)

omit [IsFinite s] in
/-- Each original image ideal has a nonzero regular local frame on Y. -/
theorem imageIdeal_nonzero_localFrame (y : Y A B J hJ s) :
    ∃ U : (Y A B J hJ s).Opens, IsAffineOpen U ∧ y ∈ U ∧
      ∃ t : Γ(Y A B J hJ s, U), t ≠ 0 ∧ IsSMulRegular Γ(Y A B J hJ s, U) t ∧
        RingHom.ker ((imageIdeal A B J hJ s).subschemeι.app U).hom = Ideal.span {t} :=
  NormalizedBlowupCover.imageIdeal_nonzero_localFrame (Base.imageIdeal A J hJ) (pi A B J hJ s)
    (Base.imageIdeal_generic_avoidance A J hJ) (Base.imageIdeal_isLocallyRankOne A J hJ) y

variable [IsNoetherianRing A] (hd : ringKrullDim A ≤ 2) (hA : IsNagataRing.{u, 0} A)
  (hfin : (Scheme.functionFieldMap s).Finite)
  (hsep : letI := Scheme.functionFieldMapAlgebra s
    Algebra.IsSeparable (Spec (.of A)).functionField (Spec (.of B)).functionField)

omit [IsFinite s] in
include hd hA hfin hsep in
/-- Actual finiteness in L follows from separability and the proved normal
locally Noetherian base normalization; none of these source properties is an input. -/
theorem pi_isFinite : IsFinite (pi A B J hJ s) := by
  let : IsLocallyNoetherian (Base.normalization A J hJ) :=
    Base.normalization_isLocallyNoetherian A J hJ hd hA
  let (x : Base.normalization A J hJ) :
      IsIntegrallyClosed ((Base.normalization A J hJ).presheaf.stalk x) :=
    (Base.normalization_normalStalks A J hJ x).2
  exact Cover.pi_isFinite (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s hfin hsep

omit [IsFinite s] in
include hd hA hfin hsep in
/-- The constructed Y is normal at all its actual stalks. -/
theorem Y_normalStalks : NormalStalks (Y A B J hJ s) := by
  let : IsLocallyNoetherian (Base.normalization A J hJ) :=
    Base.normalization_isLocallyNoetherian A J hJ hd hA
  let (x : Base.normalization A J hJ) :
      IsIntegrallyClosed ((Base.normalization A J hJ).presheaf.stalk x) :=
    (Base.normalization_normalStalks A J hJ x).2
  exact Cover.normalization_normalStalks
    (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s hfin hsep

omit [IsFinite s] in
include hd hA hfin hsep in
/-- Local Noetherianity of Y is derived from the original finite map. -/
theorem Y_isLocallyNoetherian : IsLocallyNoetherian (Y A B J hJ s) := by
  let : IsLocallyNoetherian (Base.normalization A J hJ) :=
    Base.normalization_isLocallyNoetherian A J hJ hd hA
  let : IsFinite (pi A B J hJ s) := pi_isFinite A B J hJ s hd hA hfin hsep
  exact LocallyOfFiniteType.isLocallyNoetherian (pi A B J hJ s)

include hd hA hfin hsep in
/-- Properness of the original B-map follows from the literal square. -/
theorem b_isProper : IsProper (b A B J hJ s) := by
  let : IsProper (Base.a A J hJ) := Base.a_isProper A J hJ hd hA
  let : IsFinite (Cover.pi (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s) :=
    pi_isFinite A B J hJ s hd hA hfin hsep
  exact Cover.b_isProper (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

end FiniteBase

/-- An injective original ring map yields dominance of its literal spectrum map. -/
theorem specMap_isDominant_of_injective
    {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
    (hσ : Function.Injective σ) : IsDominant (Spec.map (CommRingCat.ofHom σ)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap σ)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical σ).mpr
  rw [(RingHom.injective_iff_ker_eq_bot σ).mp hσ]
  exact bot_le

/-- Finiteness is on the literal map associated to the original ring map. -/
theorem specMap_isFinite
    {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
    (hσ : σ.Finite) : IsFinite (Spec.map (CommRingCat.ofHom σ)) :=
  IsFinite.SpecMap_iff _ |>.mpr hσ

end AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover
