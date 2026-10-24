/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.IdealPowers
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.ChartCoordinates
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite.Quotient
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.FiniteLocallyFree
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Modules.Coherent.Projective.Presentation
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence

/-!
# Normality of the ordinary rational surface blowup

The original finite generator row embeds the ordinary maximal-ideal blowup
in projective space, with its actual exceptional ideal identified with O(1).
The original power-ideal map to the normalization is bijective on global
sections by the normalized section-image theorem and ordinary scalar sections.

Integral Cartier avoidance supplies the canonical positive-power pullback
comparison. The original projection formula then identifies its adjunction
mate with the tensor of the normalization structural unit. Serre H1 vanishing
and an actual large-twist generating row kill the coherent cokernel of that
unit. The finite affine normalization is therefore an isomorphism, and the
ordinary blowup has normal stalks.

The hypotheses are a normal Noetherian Nagata local domain of dimension two
and the existing normal-modification H1-vanishing predicate. Every section,
coefficient and normalization map is the original map from the preceding
blowup and ideal-power modules. Exceptional-fibre and Hilbert-function
conclusions are separate consumers.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation
open AlgebraicGeometry.ProjectiveSpace.FromSections
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

section CategoryBoundaries

variable {C D : Type*} [Category* C] [Category* D]

private theorem normality_comp_epi {M N P : C} (f : M ⟶ N) (g : N ⟶ P)
    (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) := by
  let := hf
  let := hg
  exact epi_comp f g

private theorem normality_map_epi (F : C ⥤ D) [F.PreservesEpimorphisms]
    {M N : C} (f : M ⟶ N) (hf : Epi f) : Epi (F.map f) := by
  let := hf
  infer_instance

private theorem normality_iso_epi {M N : C} (e : M ≅ N) : Epi e.hom := inferInstance

private theorem normality_mapIso_trans_hom (F : C ⥤ D) {M N P : C} {V : D}
    (e : V ≅ F.obj M) (a : M ≅ N) (b : N ≅ P) :
    (e ≪≫ F.mapIso (a ≪≫ b)).hom = e.hom ≫ F.map a.hom ≫ F.map b.hom := by
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp]

private theorem normality_postcompose_paste {O M N P Q R : C}
    (x : O ⟶ M) (s : M ⟶ N) (a : N ⟶ P) (k : P ⟶ Q)
    (r : O ⟶ R) (η : R ⟶ P) (v : R ⟶ Q)
    (hx : x ≫ s ≫ a = r ≫ η) (hv : η ≫ k = v) :
    x ≫ s ≫ a ≫ k = r ≫ v := by
  have h := (congrArg (fun b => b ≫ k) hx).trans
    ((Category.assoc r η k).trans (congrArg (fun b => r ≫ b) hv))
  simpa only [Category.assoc] using h

private theorem normality_iso_of_cokernel_zero [Abelian C] {M N : C}
    (f : M ⟶ N) (hf : Mono f) (hQ : IsZero (cokernel f)) : IsIso f := by
  let := hf
  let : Epi f := Abelian.epi_of_cokernel_π_eq_zero f (hQ.eq_of_tgt (cokernel.π f) 0)
  exact isIso_of_mono_of_epi f

end CategoryBoundaries

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]

omit [IsDomain A] [IsLocalRing A] in
/-- The original self-algebra spectrum map is the identity. -/
theorem scalarIdentity_eq : Spec.algebraMap A A = 𝟙 (Spec (.of A)) := by
  change Spec.map (𝟙 (CommRingCat.of A)) = _
  exact Spec.map_id _

omit [IsDomain A] [IsLocalRing A] in
/-- The original identity scalar change is invertible. -/
instance scalarIdentity_isIso : IsIso (Spec.algebraMap A A) := by
  rw [scalarIdentity_eq A]
  infer_instance

/-- The literal identity scalar base change of the original ordinary blowup. -/
def selfSourceIso (hd : ringKrullDim A = 2) :
    pullback (map A hd) (Spec.algebraMap A A) ≅ source A hd :=
  asIso (pullback.fst (map A hd) (Spec.algebraMap A A))

/-- A finite row made from the original ideal generators by their native affine sheaf map. -/
def originalAffineRow {ι : Type u} (g : ι → IsLocalRing.maximalIdeal A) :
    (∐ fun _ : ι => (SheafOfModules.unit (Spec (.of A)).ringCatSheaf : (Spec (.of A)).Modules)) ⟶
      Hom.idealModule (affineCenter A (IsLocalRing.maximalIdeal A)).subschemeι :=
  (tildeFinsupp (R := CommRingCat.of A) ι).inv ≫
    tilde.map (ModuleCat.ofHom (Finsupp.linearCombination A g)) ≫
      (AffineRow.originalIdealIso (IsLocalRing.maximalIdeal A)).inv

omit [IsDomain A] in
/-- The original ideal generators make their literal affine row epimorphic. -/
theorem originalAffineRow_epi {ι : Type u} (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) : Epi (originalAffineRow A g) := by
  let X := Spec (.of A)
  let T := tilde.functor (.of A)
  let lc : ModuleCat.of A (ι →₀ A) ⟶ ModuleCat.of A (IsLocalRing.maximalIdeal A) :=
    ModuleCat.ofHom (Finsupp.linearCombination A g)
  have hlc : Epi lc := (ModuleCat.epi_iff_surjective lc).mpr
    ((_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination A).mp hg)
  let : T.PreservesEpimorphisms := CategoryTheory.Functor.preservesEpimorphisms_of_adjunction
    (tilde.adjunction (R := CommRingCat.of A))
  let eF : T.obj (ModuleCat.of A (ι →₀ A)) ≅ (∐ fun _ : ι => originalUnit X) :=
    tildeFinsupp (R := CommRingCat.of A) ι
  let eI : idealModule (affineCenter A (IsLocalRing.maximalIdeal A)).subschemeι ≅
      T.obj (ModuleCat.of A (IsLocalRing.maximalIdeal A)) :=
    AffineRow.originalIdealIso (IsLocalRing.maximalIdeal A)
  exact normality_comp_epi (C := X.Modules) eF.inv (T.map lc ≫ eI.inv)
    (normality_iso_epi (C := X.Modules) eF.symm)
    (normality_comp_epi (C := X.Modules) (T.map lc) eI.inv
      (normality_map_epi T lc hlc) (normality_iso_epi (C := X.Modules) eI.symm))

/-- The same original row under the literal identity scalar pullback. -/
def selfAffineRow {ι : Type u} (g : ι → IsLocalRing.maximalIdeal A) :
    (∐ fun _ : ι => (SheafOfModules.unit (Spec (.of A)).ringCatSheaf : (Spec (.of A)).Modules)) ⟶
      degreeOneModule (I := affineCenter A (IsLocalRing.maximalIdeal A)) (Spec.algebraMap A A) :=
  (pullbackFreeIso (Spec.algebraMap A A) ι).inv ≫
    (Modules.pullback (Spec.algebraMap A A)).map (originalAffineRow A g)

omit [IsDomain A] in
/-- The same row remains epimorphic under the original identity scalar pullback. -/
theorem selfAffineRow_epi {ι : Type u} (g : ι → IsLocalRing.maximalIdeal A)
    (hg : Submodule.span A (Set.range g) = ⊤) : Epi (selfAffineRow A g) := by
  let X := Spec (.of A)
  let F := Modules.pullback (Spec.algebraMap A A)
  let : F.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_adjunction
      (Modules.pullbackPushforwardAdjunction (Spec.algebraMap A A))
  let e := pullbackFreeIso (Spec.algebraMap A A) ι
  exact normality_comp_epi (C := X.Modules) e.inv (F.map (originalAffineRow A g))
    (normality_iso_epi (C := X.Modules) e.symm)
    (normality_map_epi F (originalAffineRow A g) (originalAffineRow_epi A g hg))

/-- The actual classifying map of the same original framed row on the identity base change. -/
def selfProjectiveMap (hd : ringKrullDim A = 2) {ι : Type u} [Finite ι]
    (g : ι → IsLocalRing.maximalIdeal A) (hg : Submodule.span A (Set.range g) = ⊤) :
    pullback (map A hd) (Spec.algebraMap A A) ⟶ ProjectiveSpace A ι := by
  let : Epi (selfAffineRow A g) := selfAffineRow_epi A g hg
  exact @OriginalRowRestriction.mapOfFramedPresentation A A _ _ _
    (IsLocalRing.maximalIdeal A) (datum A) (originalUnit (Spec (.of A))) (Iso.refl _)
    ι inferInstance (selfAffineRow A g) (selfAffineRow_epi A g hg)

/-- The original ordinary source has a closed projective map whose native coordinates
are the original finite ideal row under the identity base-change comparison. -/
def tautologicalEmbedding (hd : ringKrullDim A = 2) {ι : Type u} [Finite ι]
    (g : ι → IsLocalRing.maximalIdeal A) (hg : Submodule.span A (Set.range g) = ⊤) :
    source A hd ⟶ ProjectiveSpace A ι :=
  (selfSourceIso A hd).inv ≫ selfProjectiveMap A hd g hg

omit [IsDomain A] in
/-- The original finite ideal row gives a closed embedding of the ordinary source. -/
theorem tautologicalEmbedding_isClosedImmersion (hd : ringKrullDim A = 2)
    {ι : Type u} [Finite ι]
    (g : ι → IsLocalRing.maximalIdeal A) (hg : Submodule.span A (Set.range g) = ⊤) :
    IsClosedImmersion (tautologicalEmbedding A hd g hg) := by
  let : Epi (selfAffineRow A g) := selfAffineRow_epi A g hg
  let : IsClosedImmersion (selfProjectiveMap A hd g hg) :=
    @OriginalRowRestriction.mapOfFramedPresentation_isClosedImmersion A A _ _ _
      (IsLocalRing.maximalIdeal A) (datum A) (originalUnit (Spec (.of A))) (Iso.refl _)
      ι inferInstance (selfAffineRow A g) (selfAffineRow_epi A g hg)
  dsimp only [tautologicalEmbedding]
  infer_instance

omit [IsDomain A] in
/-- The structural triangle is the original ordinary blowdown triangle. -/
theorem tautologicalEmbedding_toSpec (hd : ringKrullDim A = 2) {ι : Type u} [Finite ι]
    (g : ι → IsLocalRing.maximalIdeal A) (hg : Submodule.span A (Set.range g) = ⊤) :
    tautologicalEmbedding A hd g hg ≫ ProjectiveSpace.toSpec A ι = map A hd := by
  let : Epi (selfAffineRow A g) := selfAffineRow_epi A g hg
  have hm : selfProjectiveMap A hd g hg ≫ ProjectiveSpace.toSpec A ι =
      pullback.snd (map A hd) (Spec.algebraMap A A) :=
    @OriginalRowRestriction.mapOfFramedPresentation_toSpec A A _ _ _
      (IsLocalRing.maximalIdeal A) (datum A) (originalUnit (Spec (.of A))) (Iso.refl _)
      ι inferInstance (selfAffineRow A g) (selfAffineRow_epi A g hg)
  have hc : pullback.fst (map A hd) (Spec.algebraMap A A) ≫ map A hd =
      pullback.snd (map A hd) (Spec.algebraMap A A) :=
    (pullback.condition (f := map A hd) (g := Spec.algebraMap A A)).trans
      ((congrArg (fun h : Spec (.of A) ⟶ Spec (.of A) =>
        pullback.snd (map A hd) (Spec.algebraMap A A) ≫ h) (scalarIdentity_eq A)).trans
          (Category.comp_id _))
  rw [tautologicalEmbedding, Category.assoc, hm, ← hc, ← Category.assoc]
  change (selfSourceIso A hd).inv ≫ (selfSourceIso A hd).hom ≫ map A hd = map A hd
  rw [Iso.inv_hom_id_assoc]

/-- The twist comparison is induced by that exact same classifying map, then by
its original identity-base-change projection. Its target is the original ideal. -/
def tautologicalEmbeddingTwistingIso (hd : ringKrullDim A = 2)
    {ι : Type u} [Finite ι]
    (g : ι → IsLocalRing.maximalIdeal A) (hg : Submodule.span A (Set.range g) = ⊤) :
    (Modules.pullback (tautologicalEmbedding A hd g hg)).obj
      (ProjectiveSpace.twistingSheaf A ι 1) ≅
        Hom.idealModule (exceptionalIdeal A hd).subschemeι := by
  let : Epi (selfAffineRow A g) := selfAffineRow_epi A g hg
  let p := pullback.fst (map A hd) (Spec.algebraMap A A)
  let e := selfSourceIso A hd
  let z := selfProjectiveMap A hd g hg
  let M := OriginalRowRestriction.affineLine (S := A) (datum A)
  let s := OriginalRowRestriction.pulledFramedFamily (datum A)
    (SheafOfModules.unit (Spec (.of A)).ringCatSheaf) (Iso.refl _) (selfAffineRow A g)
  let hM := (pulledTautologicalLine (datum A) (Spec.algebraMap A A)).property
  let hs : Epi (Sigma.desc s) := @OriginalRowRestriction.pulledFramedFamily_epi A A _ _ _
    (IsLocalRing.maximalIdeal A) (datum A) (originalUnit (Spec (.of A))) (Iso.refl _)
    ι (selfAffineRow A g) (selfAffineRow_epi A g hg)
  let : Epi (Sigma.desc s) := hs
  let et : (Modules.pullback z).obj (ProjectiveSpace.twistingSheaf A ι 1) ≅ M :=
    @twistingPullbackIsoOfFiniteFamily A inferInstance ι
      (pullback (map A hd) (Spec.algebraMap A A))
      (pullback.snd (map A hd) (Spec.algebraMap A A)) M hM inferInstance s hs
  have hp : e.inv ≫ p = 𝟙 (source A hd) := e.inv_hom_id
  exact (pullbackComp e.inv z).symm.app (ProjectiveSpace.twistingSheaf A ι 1) ≪≫
    (Modules.pullback e.inv).mapIso et ≪≫
      (pullbackComp e.inv p).app (Hom.idealModule (exceptionalIdeal A hd).subschemeι) ≪≫
        (pullbackCongr hp).app (Hom.idealModule (exceptionalIdeal A hd).subschemeι) ≪≫
          (pullbackId (source A hd)).app (Hom.idealModule (exceptionalIdeal A hd).subschemeι)

omit [IsDomain A] in
/-- Noetherianity derives the finite original generator row used by this matched embedding. -/
theorem exists_tautologicalEmbedding (hd : ringKrullDim A = 2) [IsNoetherianRing A] :
    ∃ (d : ℕ) (j : source A hd ⟶ ProjectiveSpace A (ULift.{u} (Fin (d + 1)))),
      IsClosedImmersion j ∧ j ≫ ProjectiveSpace.toSpec A (ULift.{u} (Fin (d + 1))) = map A hd ∧
        Nonempty ((Modules.pullback j).obj
          (ProjectiveSpace.twistingSheaf A (ULift.{u} (Fin (d + 1))) 1) ≅
          Hom.idealModule (exceptionalIdeal A hd).subschemeι) := by
  obtain ⟨d, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := IsLocalRing.maximalIdeal A)
  let g' : ULift.{u} (Fin (d + 1)) → IsLocalRing.maximalIdeal A :=
    fun i => Fin.cases 0 g i.down
  have hg' : Submodule.span A (Set.range g') = ⊤ := by
    apply top_unique
    rw [← hg]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨ULift.up i.succ, rfl⟩
  exact ⟨d, tautologicalEmbedding A hd g' hg',
    tautologicalEmbedding_isClosedImmersion A hd g' hg',
    tautologicalEmbedding_toSpec A hd g' hg', ⟨tautologicalEmbeddingTwistingIso A hd g' hg'⟩⟩

omit [IsDomain A] in
/-- Serre vanishing is applied on the original ordinary blowup, with the positive
projective twist identified with the original exceptional ideal. -/
theorem ordinaryIdealPower_serreH1 (hd : ringKrullDim A = 2) [IsNoetherianRing A] :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
      Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf (source A hd)
        (Hom.idealModule ((exceptionalIdeal A hd) ^ n).subschemeι)) 1) := by
  obtain ⟨d, j, hj, _, ⟨eJ⟩⟩ := exists_tautologicalEmbedding A hd
  let : IsClosedImmersion j := hj
  let X := source A hd
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let L := tautologicalLine (datum A)
  obtain ⟨B, hB⟩ := Cohomology.embeddedTensorTwist_serreVanishing j d
    (Equiv.ulift : ULift.{u} (Fin (d + 1)) ≃ Fin (d + 1)) O (affineLocallyFiniteType_unit X)
  refine ⟨B, fun n hn => ?_⟩
  let P : X.Modules := (Modules.pullback j).obj
    (ProjectiveSpace.twistingSheaf A (ULift.{u} (Fin (d + 1))) (n : ℤ))
  let e₁ : Cohomology.embeddedTensorTwist j (n : ℤ) O ≅ P :=
    CategoryTheory.MonoidalCategory.rightUnitor (C := X.Modules) P
  let e₂ : (tensorPowerLineBundle X L n).val ≅ P :=
    Surfaces.Contraction.projectivePowerIso j L eJ.symm n
  let i := (exceptionalIdeal A hd).subschemeι
  let e₃ := Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso i (datum A).cartier n
  have hker : (i.ker ^ n).subschemeι.ker = ((exceptionalIdeal A hd) ^ n).subschemeι.ker := by
    simp only [i, Scheme.IdealSheafData.ker_subschemeι]
  let e₄ := Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq
    (i.ker ^ n).subschemeι ((exceptionalIdeal A hd) ^ n).subschemeι hker
  exact Cohomology.moduleCohomology_subsingleton_of_iso (e₁ ≪≫ e₂.symm ≪≫ e₃ ≪≫ e₄) 1
    (hB (n : ℤ) (by exact_mod_cast hn) 1 (by decide))

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

private theorem scalar_value (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    (show Γ(X, ⊤) from (unitMul X a).val.app (op ⊤) (1 : Γ(X, ⊤))) = a := by
  change 1 * X.presheaf.map (𝟙 (op (⊤ : X.Opens))) a = a
  rw [CategoryTheory.Functor.map_id]
  exact one_mul a

private theorem compose_inclusion {C : Type*} [Category C]
    {O M N P : C} (s : O ⟶ M) (a : M ⟶ N) (b : N ⟶ P) (c : M ⟶ P)
    (h : a ≫ b = c) : (s ≫ a) ≫ b = s ≫ c :=
  (Category.assoc s a b).trans (congrArg (fun k => s ≫ k) h)

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]

/-- The actual ordinary exceptional ideal-power module. -/
def ordinaryIdealPower (hd : ringKrullDim A = 2) (n : ℕ) : (source A hd).Modules :=
  idealModule ((exceptionalIdeal A hd) ^ n).subschemeι

omit [IsDomain A] in
/-- The original ideal power agrees with the power of its actual closed-immersion kernel. -/
theorem ordinaryPower_kernel_eq (hd : ringKrullDim A = 2) (n : ℕ) :
    (exceptionalIdeal A hd).subschemeι.ker ^ n = (exceptionalIdeal A hd) ^ n :=
  congrArg (fun J : (source A hd).IdealSheafData => J ^ n)
    (Scheme.IdealSheafData.ker_subschemeι (exceptionalIdeal A hd))

omit [IsDomain A] in
/-- The original residue-spectrum centre has the actual ordinary exceptional kernel. -/
theorem ordinaryCentre_kernel (hd : ringKrullDim A = 2) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))).ker.comap
        (map A hd) = (exceptionalIdeal A hd).subschemeι.ker := by
  change exceptionalIdeal A hd = (exceptionalIdeal A hd).subschemeι.ker
  exact (Scheme.IdealSheafData.ker_subschemeι (exceptionalIdeal A hd)).symm

/-- The original scalar ideal-power image is the actual ordinary ideal-power kernel. -/
def ordinaryPowerScalarIso (hd : ringKrullDim A = 2) (n : ℕ) :
    idealPower (source A hd) (ordinaryCoefficients A hd) (originalUnit (source A hd))
      (IsLocalRing.maximalIdeal A) n ≅ ordinaryIdealPower A hd n := by
  let i := (exceptionalIdeal A hd).subschemeι
  let e := Surfaces.Contraction.FormalNeighborhood.idealPowerScalarIso (map A hd) i
    (IsLocalRing.maximalIdeal A) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
    Ideal.mk_ker (ordinaryCentre_kernel A hd) n
  have h : (i.ker ^ n).subschemeι.ker = ((exceptionalIdeal A hd) ^ n).subschemeι.ker := by
    exact (Scheme.IdealSheafData.ker_subschemeι _).trans
      ((ordinaryPower_kernel_eq A hd n).trans (Scheme.IdealSheafData.ker_subschemeι _).symm)
  exact e ≪≫ Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq _ _ h

omit [IsDomain A] in
/-- The scalar comparison keeps its actual inclusion into the original ordinary structure sheaf. -/
theorem ordinaryPowerScalarIso_inclusion (hd : ringKrullDim A = 2) (n : ℕ) :
    (ordinaryPowerScalarIso A hd n).hom ≫
      idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι =
    idealMultipleι (source A hd) (ordinaryCoefficients A hd) (originalUnit (source A hd))
      (IsLocalRing.maximalIdeal A ^ n) := by
  let X := source A hd
  let i := (exceptionalIdeal A hd).subschemeι
  let e := Surfaces.Contraction.FormalNeighborhood.idealPowerScalarIso (map A hd) i
    (IsLocalRing.maximalIdeal A) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
    Ideal.mk_ker (ordinaryCentre_kernel A hd) n
  have h : (i.ker ^ n).subschemeι.ker = ((exceptionalIdeal A hd) ^ n).subschemeι.ker :=
    (Scheme.IdealSheafData.ker_subschemeι _).trans
      ((ordinaryPower_kernel_eq A hd n).trans (Scheme.IdealSheafData.ker_subschemeι _).symm)
  let c := Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq
    (i.ker ^ n).subschemeι ((exceptionalIdeal A hd) ^ n).subschemeι h
  have hc : c.hom ≫ idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι =
      idealInclusion (i.ker ^ n).subschemeι :=
    Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq_hom_inclusion
      (i.ker ^ n).subschemeι ((exceptionalIdeal A hd) ^ n).subschemeι h
  have he : e.hom ≫ idealInclusion (i.ker ^ n).subschemeι =
      idealMultipleι X (ordinaryCoefficients A hd) (originalUnit X)
        (IsLocalRing.maximalIdeal A ^ n) :=
    Surfaces.Contraction.FormalNeighborhood.idealPowerScalarIso_hom_inclusion
      (map A hd) i (IsLocalRing.maximalIdeal A) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
      Ideal.mk_ker (ordinaryCentre_kernel A hd) n
  exact (compose_inclusion e.hom c.hom
    (idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι)
      (idealInclusion (i.ker ^ n).subschemeι) hc).trans he

/-- Every original scalar in m^n gives its actual ordinary ideal-power section. -/
def ordinaryPowerScalarSection (hd : ringKrullDim A = 2) (n : ℕ)
    (a : ↥(IsLocalRing.maximalIdeal A ^ n)) :
    originalUnit (source A hd) ⟶ ordinaryIdealPower A hd n :=
  idealMultipleScalar (source A hd) (ordinaryCoefficients A hd) (originalUnit (source A hd))
      (IsLocalRing.maximalIdeal A ^ n) a ≫ (ordinaryPowerScalarIso A hd n).hom

omit [IsDomain A] in
/-- The original scalar-power section retains its structural scalar after inclusion. -/
theorem ordinaryPowerScalarSection_inclusion (hd : ringKrullDim A = 2)
    (n : ℕ) (a : ↥(IsLocalRing.maximalIdeal A ^ n)) :
    ordinaryPowerScalarSection A hd n a ≫
      idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι =
        unitMul (source A hd) (ordinaryCoefficients A hd (a : A)) := by
  have h := compose_inclusion
    (idealMultipleScalar (source A hd) (ordinaryCoefficients A hd) (originalUnit (source A hd))
      (IsLocalRing.maximalIdeal A ^ n) a)
    (ordinaryPowerScalarIso A hd n).hom
    (idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι) _
    (ordinaryPowerScalarIso_inclusion A hd n)
  exact h.trans ((idealMultipleScalar_ι (source A hd) (ordinaryCoefficients A hd)
    (originalUnit (source A hd)) (IsLocalRing.maximalIdeal A ^ n) a).trans
      (globalScalarEndomorphism_unit (source A hd) (ordinaryCoefficients A hd (a : A))))

/-- Powers commute with the literal normalization inverse image. -/
theorem powerCentre_comap (hd : ringKrullDim A = 2) (n : ℕ) :
    (normalizedExceptionalIdeal A hd) ^ n = ((exceptionalIdeal A hd) ^ n).comap (nu A hd) :=
  (Scheme.IdealSheafData.comap_pow (exceptionalIdeal A hd) n (nu A hd)).symm

/-- The actual map of the two original power-centre subschemes. -/
def powerCentreMap (hd : ringKrullDim A = 2) (n : ℕ) :
    ((normalizedExceptionalIdeal A hd) ^ n).subscheme ⟶
      ((exceptionalIdeal A hd) ^ n).subscheme :=
  ((normalizedExceptionalIdeal A hd) ^ n).subschemeMap ((exceptionalIdeal A hd) ^ n) (nu A hd)
    (by rw [powerCentre_comap]; exact ((exceptionalIdeal A hd) ^ n).le_map_comap (nu A hd))

/-- The two original power-centre inclusions retain their normalization triangle. -/
theorem powerCentreMap_ι (hd : ringKrullDim A = 2) (n : ℕ) :
    powerCentreMap A hd n ≫ ((exceptionalIdeal A hd) ^ n).subschemeι =
      ((normalizedExceptionalIdeal A hd) ^ n).subschemeι ≫ nu A hd :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The original kernel map along the actual normalization, before normality of X is known. -/
def idealPowerNormalizationUnit (hd : ringKrullDim A = 2) (n : ℕ) :
    ordinaryIdealPower A hd n ⟶ (Modules.pushforward (nu A hd)).obj (normalizedIdealPower A hd n) :=
  idealPushforwardMap ((exceptionalIdeal A hd) ^ n).subschemeι
    ((normalizedExceptionalIdeal A hd) ^ n).subschemeι (nu A hd) (powerCentreMap A hd n)
      (powerCentreMap_ι A hd n)

/-- Its original inclusion square is the structural normalization unit. -/
theorem idealPowerNormalizationUnit_inclusion (hd : ringKrullDim A = 2) (n : ℕ) :
    idealPowerNormalizationUnit A hd n ≫
      (Modules.pushforward (nu A hd)).map
        (idealInclusion ((normalizedExceptionalIdeal A hd) ^ n).subschemeι) =
      idealInclusion ((exceptionalIdeal A hd) ^ n).subschemeι ≫ structureModuleMap (nu A hd) :=
  idealPushforwardMap_inclusion _ _ _ _ _

/-- The two original coefficient maps commute with the actual normalization ring map. -/
theorem coefficients_nu (hd : ringKrullDim A = 2) :
    (nu A hd).appTop.hom.comp (ordinaryCoefficients A hd) = coefficients A hd := by
  change ((nu A hd).appTop.hom.comp (map A hd).appTop.hom).comp
      (Scheme.ΓSpecIso (.of A)).inv.hom =
    (nu A hd ≫ map A hd).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- The original power-normalization map is bijective on actual global sections.
Its surjectivity uses the proved normalized section image and actual ordinary scalar sections. -/
theorem idealPowerNormalizationUnit_global_bijective (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Function.Bijective ((idealPowerNormalizationUnit A hd n).val.app (op ⊤)) := by
  let X := source A hd
  let Y := normalization A hd
  let f := nu A hd
  let i := ((exceptionalIdeal A hd) ^ n).subschemeι
  let j := ((normalizedExceptionalIdeal A hd) ^ n).subschemeι
  let v := idealPowerNormalizationUnit A hd n
  let : IsFinite f := nu_isFinite A hd hA
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have htriangle (s : Γ(ordinaryIdealPower A hd n, ⊤)) :
      (show Γ(Y, ⊤) from ((Modules.pushforward f).map (idealInclusion j)).val.app (op ⊤)
        (v.val.app (op ⊤) s)) =
      f.appTop (show Γ(X, ⊤) from (idealInclusion i).val.app (op ⊤) s) :=
    congrArg (fun k : ordinaryIdealPower A hd n ⟶
      (Modules.pushforward f).obj (originalUnit Y) => k.val.app (op ⊤) s)
      (idealPowerNormalizationUnit_inclusion A hd n)
  have hin : Function.Injective
      (((Modules.pushforward f).map (idealInclusion j)).val.app (op ⊤)) :=
    moduleHom_app_injective ((Modules.pushforward f).map (idealInclusion j)) ⊤
  constructor
  · intro s t hst
    apply moduleHom_app_injective (idealInclusion i) ⊤
    apply f.app_injective ⊤
    exact (htriangle s).symm.trans
      ((congrArg (fun z => ((Modules.pushforward f).map (idealInclusion j)).val.app (op ⊤) z)
        hst).trans (htriangle t))
  · intro t
    let b : Γ(Y, ⊤) :=
      ((Modules.pushforward f).map (idealInclusion j)).val.app (op ⊤) t
    obtain ⟨a, ha⟩ := (coefficients_bijective A hd hA).2 b
    have haker : coefficients A hd a ∈ RingHom.ker j.appTop.hom := by
      let v := (idealSectionsEquiv j ⊤).toEquiv (show Γ(idealModule j, ⊤) from t)
      have hv : (v : Γ(Y, ⊤)) = b :=
        idealSectionsEquiv_val j ⊤ (show Γ(idealModule j, ⊤) from t)
      have hb : b ∈ RingHom.ker j.appTop.hom :=
        (congrArg (fun z : Γ(Y, ⊤) => z ∈ RingHom.ker j.appTop.hom) hv).mp v.property
      exact (congrArg (fun z : Γ(Y, ⊤) => z ∈ RingHom.ker j.appTop.hom) ha.symm).mp hb
    have ham : a ∈ IsLocalRing.maximalIdeal A ^ n := by
      rw [← normalizedIdealPower_sectionImage A hd hA hRat n]
      exact haker
    let s := unitHomGlobalSectionsEquiv X (ordinaryIdealPower A hd n)
      (ordinaryPowerScalarSection A hd n ⟨a, ham⟩)
    refine ⟨s, hin ?_⟩
    have hs : (show Γ(X, ⊤) from (idealInclusion i).val.app (op ⊤) s) =
        ordinaryCoefficients A hd a := by
      have h := congrArg (fun k : originalUnit X ⟶ originalUnit X =>
        (show Γ(X, ⊤) from k.val.app (op ⊤) (1 : Γ(X, ⊤))))
          (ordinaryPowerScalarSection_inclusion A hd n ⟨a, ham⟩)
      exact h.trans (scalar_value X (ordinaryCoefficients A hd a))
    exact (htriangle s).trans ((congrArg f.appTop hs).trans
      ((congrArg (fun φ : A →+* Γ(Y, ⊤) => φ a) (coefficients_nu A hd)).trans ha))

omit [IsDomain A] in
/-- Every original ordinary ideal power is a line module through native Cartier multiplication. -/
theorem ordinaryIdealPower_locallyRankOne (hd : ringKrullDim A = 2) (n : ℕ) :
    IsLocallyRankOne (source A hd) (ordinaryIdealPower A hd n) := by
  let X := source A hd
  let i := (exceptionalIdeal A hd).subschemeι
  let L := ProjectivePresentation.tautologicalLine (datum A)
  let P := tensorPowerLineBundle X L n
  let e := Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso i (datum A).cartier n
  have h : (i.ker ^ n).subschemeι.ker = ((exceptionalIdeal A hd) ^ n).subschemeι.ker := by
    exact (Scheme.IdealSheafData.ker_subschemeι _).trans
      ((ordinaryPower_kernel_eq A hd n).trans (Scheme.IdealSheafData.ker_subschemeι _).symm)
  let c := Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq
    (i.ker ^ n).subschemeι ((exceptionalIdeal A hd) ^ n).subschemeι h
  exact isLocallyRankOne_of_iso X (e ≪≫ c) P.property

/-- The actual normalization generic point avoids every positive ordinary exceptional power. -/
theorem normalization_avoids_positivePower (hd : ringKrullDim A = 2) (n : ℕ) :
    ¬ Set.range (nu A hd) ⊆ Set.range ((exceptionalIdeal A hd) ^ (n + 1)).subschemeι := by
  have havoid : genericPoint (Spec (.of A)) ∉
      ((affineCenter A (IsLocalRing.maximalIdeal A)).support : Set (Spec (.of A))) := by
    rw [support_affineCenter, PrimeSpectrum.zeroLocus_eq_singleton]
    exact (closedPoint_ne_generic A hd).symm
  intro h
  have hx := h (Set.mem_range_self (genericPoint (normalization A hd)))
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow_succ,
    Scheme.map_genericPoint_of_isDominant (normalization A hd) (nu A hd)] at hx
  change genericPoint (source A hd) ∈
    ((affineCenter A (IsLocalRing.maximalIdeal A)).comap (map A hd)).support at hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  change map A hd (genericPoint (source A hd)) ∈
    (affineCenter A (IsLocalRing.maximalIdeal A)).support at hx
  rw [Scheme.map_genericPoint_of_isDominant (source A hd) (map A hd)] at hx
  exact havoid hx

/-- The original full power-centre square is Cartesian. -/
theorem powerCentre_isPullback (hd : ringKrullDim A = 2) (n : ℕ) :
    IsPullback (powerCentreMap A hd n) ((normalizedExceptionalIdeal A hd) ^ n).subschemeι
      ((exceptionalIdeal A hd) ^ n).subschemeι (nu A hd) :=
  (isPullback_of_isClosedImmersion ((normalizedExceptionalIdeal A hd) ^ n).subschemeι
    ((exceptionalIdeal A hd) ^ n).subschemeι (powerCentreMap A hd n) (nu A hd)
    (powerCentreMap_ι A hd n).symm (by
      simpa only [Scheme.IdealSheafData.ker_subschemeι] using
        (powerCentre_comap A hd n).symm)).flip

/-- Integral avoidance identifies the canonical positive power pullback. -/
def normalizedPositivePowerPullbackIso (hd : ringKrullDim A = 2) (n : ℕ) :
    (Modules.pullback (nu A hd)).obj (ordinaryIdealPower A hd (n + 1)) ≅
      normalizedIdealPower A hd (n + 1) := by
  let i := ((exceptionalIdeal A hd) ^ (n + 1)).subschemeι
  let j := ((normalizedExceptionalIdeal A hd) ^ (n + 1)).subschemeι
  let a := powerCentreMap A hd (n + 1)
  let h := powerCentreMap_ι A hd (n + 1)
  have hmap : IsIso (idealPullbackMap i j (nu A hd) a h) :=
    idealPullbackMap_isIso_of_integral_avoidance i j (nu A hd) a h
      (powerCentre_isPullback A hd (n + 1)) (ordinaryIdealPower_locallyRankOne A hd (n + 1))
      (normalization_avoids_positivePower A hd n)
  exact @asIso (normalization A hd).Modules inferInstance
    ((Modules.pullback (nu A hd)).obj (ordinaryIdealPower A hd (n + 1)))
    (normalizedIdealPower A hd (n + 1)) (idealPullbackMap i j (nu A hd) a h) hmap

/-- The canonical power pullback is adjoint to the same original ideal-kernel map. -/
theorem normalizedPositivePowerPullbackIso_adjoint (hd : ringKrullDim A = 2) (n : ℕ) :
    (Modules.pullbackPushforwardAdjunction (nu A hd)).unit.app
        (ordinaryIdealPower A hd (n + 1)) ≫
      (Modules.pushforward (nu A hd)).map (normalizedPositivePowerPullbackIso A hd n).hom =
        idealPowerNormalizationUnit A hd (n + 1) := by
  let adj := Modules.pullbackPushforwardAdjunction (nu A hd)
  let i := ((exceptionalIdeal A hd) ^ (n + 1)).subschemeι
  let j := ((normalizedExceptionalIdeal A hd) ^ (n + 1)).subschemeι
  let f := idealPullbackMap i j (nu A hd) (powerCentreMap A hd (n + 1))
    (powerCentreMap_ι A hd (n + 1))
  have he : adj.homEquiv (ordinaryIdealPower A hd (n + 1))
      (normalizedIdealPower A hd (n + 1)) f =
        adj.unit.app (ordinaryIdealPower A hd (n + 1)) ≫ (Modules.pushforward (nu A hd)).map f :=
    adj.homEquiv_unit (ordinaryIdealPower A hd (n + 1))
      (normalizedIdealPower A hd (n + 1)) f
  exact he.symm.trans (idealPullbackMap_adjoint i j (nu A hd)
    (powerCentreMap A hd (n + 1)) (powerCentreMap_ι A hd (n + 1)))

/-- The actual finite-locally-free projection formula, followed by the canonical
Cartier pullback comparison, targets the original normalized ideal power. -/
def normalizedPositivePowerProjectionIso (hd : ringKrullDim A = 2) (n : ℕ) :
    (moduleTensorLeftFunctor (source A hd) (ordinaryIdealPower A hd (n + 1))).obj
        ((Modules.pushforward (nu A hd)).obj (originalUnit (normalization A hd))) ≅
      (Modules.pushforward (nu A hd)).obj (normalizedIdealPower A hd (n + 1)) := by
  let X := source A hd
  let Y := normalization A hd
  let P := ordinaryIdealPower A hd (n + 1)
  let : IsFiniteLocallyFree X P :=
    isFiniteLocallyFree_of_isLocallyRankOne (ordinaryIdealPower_locallyRankOne A hd (n + 1))
  let e : (moduleTensorLeftFunctor Y ((Modules.pullback (nu A hd)).obj P)).obj (originalUnit Y) ≅
      normalizedIdealPower A hd (n + 1) :=
    CategoryTheory.MonoidalCategory.rightUnitor (C := Y.Modules)
      ((Modules.pullback (nu A hd)).obj P) ≪≫
      normalizedPositivePowerPullbackIso A hd n
  exact projectionFormulaIso (nu A hd) P (originalUnit Y) ≪≫
    (Modules.pushforward (nu A hd)).mapIso e

/-- The finite normalization has the original coherent structural cokernel. -/
theorem normalizationCokernel_coherent (hd : ringKrullDim A = 2) [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) :
    affineLocallyFiniteType (source A hd)
      (Modules.Coherent.Support.quotient (nu A hd)) := by
  let : IsFinite (nu A hd) := nu_isFinite A hd hA
  exact Modules.Coherent.Support.quotient_coherent (nu A hd)

/-- An affine morphism is detected by its original structure-module unit.
The normality argument supplies invertibility of that same unit. -/
private theorem affine_isIso_of_original_unit {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (h : IsIso (structureModuleMap f)) : IsIso f := by
  let := h
  have happ (U : X.Opens) : IsIso (f.app U) := by
    have hm : IsIso ((structureModuleMap f).app U) :=
      (Scheme.Modules.Hom.isIso_iff_isIso_app.mp h) U
    let := hm
    apply (ConcreteCategory.isIso_iff_bijective (f.app U)).mpr
    exact ConcreteCategory.bijective_of_isIso ((structureModuleMap f).app U)
  have hcover : iSup (fun U : X.affineOpens => U.1) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun U : X.affineOpens => U.1) hcover
  intro U
  exact (isIso_morphismRestrict_iff_isIso_app f U.2).mpr (happ U.1)

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- The original finite-free row of a coherent projective twist, constructed from
an actual negative-twist presentation and the native inverse-twist comparison. -/
private theorem exists_largeTwist_row {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    {X : Scheme.{u}} (j : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion j]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ∃ (κ : Type u) (_ : Finite κ)
      (s : κ → (originalUnit X ⟶ Cohomology.embeddedTensorTwist j (n : ℤ) M)),
        Epi (Sigma.desc s) := by
  obtain ⟨n, hn, κ, hκ, π, hπ, _⟩ :=
    Modules.Coherent.Projective.exists_uniformNegativeTwistEpimorphism A ι j M hM B
  let := hκ
  let := hπ
  let P : X.Modules := (Modules.pullback j).obj (ProjectiveSpace.twistingSheaf A ι (n : ℤ))
  let D : X.Modules := (Modules.pullback j).obj (ProjectiveSpace.twistingSheaf A ι (-(n : ℤ)))
  let T := moduleTensorLeftFunctor X P
  let : IsFiniteLocallyFree X P := inferInstance
  let : T.Additive := moduleTensorLeftFunctor_additive X P
  let : T.PreservesHomology := moduleTensorLeft_preservesHomology P
  let : PreservesFiniteColimits T :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology T
  let : IsIso (pullbackTensorMap j (ProjectiveSpace.twistingSheaf A ι (n : ℤ))
      (ProjectiveSpace.twistingSheaf A ι (-(n : ℤ)))) :=
    Pullback.Tensor.pullbackTensorMap_isIso j _ _
  let et : T.obj D ≅ originalUnit X :=
    (asIso (pullbackTensorMap j (ProjectiveSpace.twistingSheaf A ι (n : ℤ))
      (ProjectiveSpace.twistingSheaf A ι (-(n : ℤ))))).symm ≪≫
    (Modules.pullback j).mapIso (ProjectiveSpace.twistingTensorIso A ι (n : ℤ) (-(n : ℤ))) ≪≫
    eqToIso (congrArg (fun d : ℤ => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι d)) (add_neg_cancel (n : ℤ))) ≪≫
    (Modules.pullback j).mapIso (ProjectiveSpace.twistingZeroIso A ι) ≪≫ pullbackUnitIso j
  let e : (∐ fun _ : κ => originalUnit X) ≅ T.obj (∐ fun _ : κ => D) :=
    Sigma.mapIso (fun _ : κ => et.symm) ≪≫ (PreservesCoproduct.iso T (fun _ : κ => D)).symm
  let r : (∐ fun _ : κ => originalUnit X) ⟶ T.obj M := e.hom ≫ T.map π
  let s := fun k : κ => Sigma.ι (fun _ : κ => originalUnit X) k ≫ r
  have hr : Sigma.desc s = r := by
    apply Sigma.hom_ext
    intro k
    exact Sigma.ι_comp_desc s k
  have hT : Epi (T.map π) := preserves_epi_of_preservesColimit T π
  let := hT
  have hre : Epi r := epi_comp e.hom (T.map π)
  exact ⟨n, hn, κ, hκ, s, hr.symm ▸ hre⟩

/-- The projection formula intertwines the tensor of the original structural
unit with the original geometric adjunction unit through the original right unitor. -/
private theorem projection_unit_square {Y X : Scheme.{u}} (f : Y ⟶ X) (P : X.Modules) :
    (moduleTensorLeftFunctor X P).map (Hom.structureModuleMap f) ≫
      projectionFormulaMap f P (originalUnit Y) ≫
        (Modules.pushforward f).map
          (rightUnitor (C := Y.Modules) ((Modules.pullback f).obj P)).hom =
      (rightUnitor (C := X.Modules) P).hom ≫
        (Modules.pullbackPushforwardAdjunction f).unit.app P := by
  apply moduleTensor_hom_ext
  intro U p a
  let Q := (Modules.pullback f).obj P
  let η := (Modules.pullbackPushforwardAdjunction f).unit.app P
  let r := (rightUnitor (C := Y.Modules) Q).hom
  let L := fun z : Γ(tensorSheaf X P ((Modules.pushforward f).obj (originalUnit Y)), U) =>
    ((Modules.pushforward f).map r).val.app (op U)
      ((projectionFormulaMap f P (originalUnit Y)).val.app (op U) z)
  have h₀ := congrArg L
    (moduleTensorLeftFunctor_map_section P (Hom.structureModuleMap f) U p a)
  have h₁ := congrArg (fun z : Γ(tensorSheaf Y Q (originalUnit Y), f ⁻¹ᵁ U) =>
    r.val.app (op (f ⁻¹ᵁ U)) z)
      (projectionFormulaMap_section f P (originalUnit Y) U p (f.app U a))
  have h₂ := tensorRightUnitIso_hom_section Y Q (f ⁻¹ᵁ U)
    (η.val.app (op U) p) (f.app U a)
  have h₃ := (η.val.app (op U)).hom.map_smul a p
  have h₄ := congrArg (fun z : Γ(P, U) => η.val.app (op U) z)
    (tensorRightUnitIso_hom_section X P U p a).symm
  exact h₀.trans (h₁.trans (h₂.trans (h₃.symm.trans h₄)))

/-- Surjectivity of the first actual section map and H1 of the first term kill the
original sections of the cokernel term. The H1 hypothesis is essential here. -/
private theorem quotient_sections_subsingleton {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hf : Function.Surjective (S.f.val.app (op ⊤)))
    (hH : Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X S.X₁) 1)) :
    Subsingleton Γ(S.X₃, ⊤) := by
  let := hH
  let α := RingHom.id Γ(X, ⊤)
  let := Cohomology.moduleCohomologyModuleOfHom X α S.X₃ 0
  let := Cohomology.moduleCohomologyModuleOfHom X α S.X₁ (0 + 1)
  have hg : Function.Surjective (S.g.val.app (op ⊤)) :=
    Cohomology.surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero
      (X := X) α S hS (by
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _)
  have hz (z : Γ(S.X₃, ⊤)) : z = 0 := by
    obtain ⟨y, hy⟩ := hg z
    obtain ⟨x, hx⟩ := hf y
    have hzero := congrArg (fun k : S.X₁ ⟶ S.X₃ => k.val.app (op ⊤) x) S.zero
    exact hy.symm.trans ((congrArg (fun t => S.g.val.app (op ⊤) t) hx).symm.trans hzero)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- An actual epimorphic section row with zero original sections has zero target. -/
private theorem zero_of_original_row {X : Scheme.{u}} {M : X.Modules} {ι : Type u}
    (s : ι → (originalUnit X ⟶ M)) (hs : Epi (Sigma.desc s))
    (hΓ : Subsingleton Γ(M, ⊤)) : IsZero M := by
  let := hs
  have hentry (i : ι) : s i = 0 :=
    (unitHomGlobalSectionsEquiv X M).injective (@Subsingleton.elim _ hΓ _ _)
  have hrow : Sigma.desc s = 0 := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, hentry, comp_zero]
  apply (IsZero.iff_id_eq_zero M).mpr
  apply (cancel_epi (Sigma.desc s)).mp
  rw [Category.comp_id, comp_zero]
  exact hrow

/-- Actual invertible tensoring reflects zero objects through its native dual equivalence. -/
private theorem zero_of_line_tensor {X : Scheme.{u}} (L : LineBundle X) (M : X.Modules)
    (h : IsZero ((moduleTensorLeftFunctor X L.val).obj M)) : IsZero M := by
  let F := (lineBundleDualTensorEquivalence X L).inverse
  let : F.Additive := moduleTensorLeftFunctor_additive X L.val
  have hF : IsZero (F.obj M) := h
  apply (IsZero.iff_id_eq_zero M).mpr
  apply F.map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hF.eq_of_tgt _ _

end AlgebraicGeometry.Scheme.RationalSingularities

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

private theorem surjective_of_equiv_square {S T U V : Type*}
    (eS : S ≃ U) (eT : T ≃ V) (f : S → T) (g : U → V)
    (h : ∀ x, eT (f x) = g (eS x)) (hg : Function.Surjective g) : Function.Surjective f := by
  intro y
  obtain ⟨z, hz⟩ := hg (eT y)
  refine ⟨eS.symm z, eT.injective ?_⟩
  rw [h, Equiv.apply_symm_apply, hz]

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]

/-- The actual projection formula identifies the twisted structural unit with
exactly the original ideal-power normalization map. -/
theorem positivePowerProjection_unit (hd : ringKrullDim A = 2) (n : ℕ) :
    (moduleTensorLeftFunctor (source A hd) (ordinaryIdealPower A hd (n + 1))).map
        (Hom.structureModuleMap (nu A hd)) ≫ (normalizedPositivePowerProjectionIso A hd n).hom =
      (rightUnitor (C := (source A hd).Modules) (ordinaryIdealPower A hd (n + 1))).hom ≫
        idealPowerNormalizationUnit A hd (n + 1) := by
  let X := source A hd
  let Y := normalization A hd
  let P := ordinaryIdealPower A hd (n + 1)
  let f := nu A hd
  let T := moduleTensorLeftFunctor X P
  let : IsFiniteLocallyFree X P :=
    isFiniteLocallyFree_of_isLocallyRankOne (ordinaryIdealPower_locallyRankOne A hd (n + 1))
  let e := normalizedPositivePowerPullbackIso A hd n
  let σ := projectionFormulaMap f P (originalUnit Y)
  let a := (Modules.pushforward f).map
    (rightUnitor (C := Y.Modules) ((Modules.pullback f).obj P)).hom
  let k := (Modules.pushforward f).map e.hom
  let μ : originalUnit X ⟶ (Modules.pushforward f).obj (originalUnit Y) :=
    Hom.structureModuleMap f
  let r := (rightUnitor (C := X.Modules) P).hom
  let η := (Modules.pullbackPushforwardAdjunction f).unit.app P
  let v := idealPowerNormalizationUnit A hd (n + 1)
  have hproj : (normalizedPositivePowerProjectionIso A hd n).hom = σ ≫ a ≫ k :=
    normality_mapIso_trans_hom (Modules.pushforward f)
      (projectionFormulaIso f P (originalUnit Y))
      (rightUnitor (C := Y.Modules) ((Modules.pullback f).obj P)) e
  have hpf : T.map μ ≫ σ ≫ a = r ≫ η := projection_unit_square f P
  have hadj : η ≫ k = v := normalizedPositivePowerPullbackIso_adjoint A hd n
  exact (congrArg (fun z => T.map μ ≫ z) hproj).trans
    (normality_postcompose_paste (C := X.Modules) (T.map μ) σ a k r η v hpf hadj)

/-- The same positive-twist structural unit is surjective on original global sections. -/
theorem normalization_twistedUnit_global_surjective (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (n : ℕ) :
    Function.Surjective (((moduleTensorLeftFunctor (source A hd)
      (ordinaryIdealPower A hd (n + 1))).map
        (Hom.structureModuleMap (nu A hd))).val.app (op ⊤)) := by
  let X := source A hd
  let Y := normalization A hd
  let P := ordinaryIdealPower A hd (n + 1)
  let T := moduleTensorLeftFunctor X P
  let μ := Hom.structureModuleMap (nu A hd)
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let eS := ((ev.mapIso (rightUnitor (C := X.Modules) P)).toLinearEquiv).toEquiv
  let eT := ((ev.mapIso (normalizedPositivePowerProjectionIso A hd n)).toLinearEquiv).toEquiv
  apply surjective_of_equiv_square eS eT (fun s => (T.map μ).val.app (op ⊤) s)
    (fun s => (idealPowerNormalizationUnit A hd (n + 1)).val.app (op ⊤) s)
    (fun s => ?_) (idealPowerNormalizationUnit_global_bijective A hd hA hRat (n + 1)).2
  exact congrArg (fun k : T.obj (originalUnit X) ⟶
    (Modules.pushforward (nu A hd)).obj (normalizedIdealPower A hd (n + 1)) =>
      k.val.app (op ⊤) s) (positivePowerProjection_unit A hd n)

/-- The literal normalization cokernel has an actual finite row after an arbitrarily
large positive original ideal twist. The row is derived from projective presentation. -/
theorem exists_normalizationCokernel_power_row (hd : ringKrullDim A = 2) [IsNoetherianRing A]
    (hA : IsNagataRing.{u, 0} A) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ∃ (κ : Type u) (_ : Finite κ)
      (s : κ → (originalUnit (source A hd) ⟶
        (moduleTensorLeftFunctor (source A hd) (ordinaryIdealPower A hd n)).obj
          (Modules.Coherent.Support.quotient (nu A hd)))), Epi (Sigma.desc s) := by
  obtain ⟨d, j, hj, _, ⟨eJ⟩⟩ := exists_tautologicalEmbedding A hd
  let := hj
  let X := source A hd
  let Q := Modules.Coherent.Support.quotient (nu A hd)
  obtain ⟨n, hn, κ, hκ, s, hs⟩ := exists_largeTwist_row j Q
    (normalizationCokernel_coherent A hd hA) B
  let := hκ
  let := hs
  let L := ProjectivePresentation.tautologicalLine (datum A)
  let i := (exceptionalIdeal A hd).subschemeι
  let e₁ := Surfaces.Contraction.projectivePowerIso j L eJ.symm n
  let e₂ := Surfaces.Contraction.FormalNeighborhood.cartierIdealPowerIso i (datum A).cartier n
  have hker : (i.ker ^ n).subschemeι.ker = ((exceptionalIdeal A hd) ^ n).subschemeι.ker := by
    exact (Scheme.IdealSheafData.ker_subschemeι _).trans
      ((ordinaryPower_kernel_eq A hd n).trans (Scheme.IdealSheafData.ker_subschemeι _).symm)
  let e₃ := Surfaces.Contraction.FormalNeighborhood.idealModuleIsoOfKernelEq
    (i.ker ^ n).subschemeι ((exceptionalIdeal A hd) ^ n).subschemeι hker
  let eP := e₁.symm ≪≫ e₂ ≪≫ e₃
  let e := (moduleTensorRightFunctor X Q).mapIso eP
  exact ⟨n, hn, κ, hκ, fun k => s k ≫ e.hom,
    @AlgebraicGeometry.ProjectiveSpace.FromSections.family_comp_iso_epi
      (I := κ) (X := X) (M := Cohomology.embeddedTensorTwist j (n : ℤ) Q)
      (N := (moduleTensorLeftFunctor X (ordinaryIdealPower A hd n)).obj Q)
      (s := s) (e := e) hs⟩

/-- The actual coherent cokernel of the original normalization unit vanishes.
Both the original H0 surjection and the ordinary-source Serre H1 term are used. -/
theorem normalizationCokernel_isZero (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    IsZero (Modules.Coherent.Support.quotient (nu A hd)) := by
  obtain ⟨B, hB⟩ := ordinaryIdealPower_serreH1 A hd
  obtain ⟨N, hN, κ, hκ, s, hs⟩ := exists_normalizationCokernel_power_row A hd hA B
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ((Nat.zero_le B).trans_lt hN))
  let X := source A hd
  let Y := normalization A hd
  let f := nu A hd
  let : IsFinite f := nu_isFinite A hd hA
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  let Q := Modules.Coherent.Support.quotient f
  let P := ordinaryIdealPower A hd (n + 1)
  let L : LineBundle X := ⟨P, ordinaryIdealPower_locallyRankOne A hd (n + 1)⟩
  let : IsFiniteLocallyFree X P := isFiniteLocallyFree_of_isLocallyRankOne L.property
  let S := Modules.Coherent.Support.sequence f
  have hS := Modules.Coherent.Support.sequence_shortExact f
  let T := moduleTensorLeftFunctor X P
  have hST : (S.map T).ShortExact := tensor_shortExact_finiteLocallyFree P S hS
  have hH : Subsingleton (Sheaf.H.{u + 1}
      (Cohomology.moduleAddSheaf X ((S.map T).X₁)) 1) :=
    Cohomology.moduleCohomology_subsingleton_of_iso
      (rightUnitor (C := X.Modules) P).symm 1 (hB (n + 1) hN.le)
  have hΓ : Subsingleton Γ(T.obj Q, ⊤) := quotient_sections_subsingleton (S.map T) hST
    (normalization_twistedUnit_global_surjective A hd hA hRat n) hH
  have hTQ : IsZero (T.obj Q) := zero_of_original_row s hs hΓ
  exact zero_of_line_tensor L Q hTQ

/-- The original finite affine normalization arrow is an isomorphism, derived
from the actual structural cokernel. -/
theorem normalization_isIso (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    IsIso (nu A hd) := by
  let f := nu A hd
  let : IsFinite f := nu_isFinite A hd hA
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  let X := source A hd
  let μ : originalUnit X ⟶ (Modules.pushforward f).obj (originalUnit (normalization A hd)) :=
    Modules.Coherent.Support.unitMap f
  have hQ : IsZero (cokernel μ) := normalizationCokernel_isZero A hd hA hRat
  have hμ : IsIso μ := normality_iso_of_cokernel_zero (C := X.Modules) μ
    (Modules.Coherent.Support.unitMap_mono f) hQ
  exact affine_isIso_of_original_unit f hμ

/-- The literal ordinary maximal-ideal blowup has normal actual stalks. -/
theorem ordinary_normalStalks (hd : ringKrullDim A = 2)
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    NormalStalks (source A hd) := by
  let : IsIso (nu A hd) := normalization_isIso A hd hA hRat
  intro x
  let y := inv (nu A hd) x
  let : IsIntegrallyClosed ((normalization A hd).presheaf.stalk y) :=
    (normalization_normalStalks A hd y).2
  let e := (asIso ((inv (nu A hd)).stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
