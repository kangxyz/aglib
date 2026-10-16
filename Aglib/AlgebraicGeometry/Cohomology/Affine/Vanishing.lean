/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cech.Cocycles
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.ExactSequences
public import Aglib.AlgebraicGeometry.Cohomology.Cech.InjectiveCoefficients
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Cech.AffineHigherExactness
public import Aglib.AlgebraicGeometry.Cohomology.Affine.DerivedGlobalSections
/-!
# Higher derived global sections of affine quasicoherent module sheaves

For an arbitrary commutative ring and quasicoherent module sheaf `M` on
`Spec R`, `AffineDerived.isZero_rightDerived_globalSections_succ` proves
vanishing of the original `moduleSpecΓFunctor.rightDerived (n + 1)` for
every natural `n`. The stronger
`AffineDerived.globalSections_injectiveResolution_exact_succ` proves
exactness after applying original global sections to any actual injective
resolution in the ambient category of all module sheaves.

The proof first obtains actual section lifts from degree-one original
Cech exactness on cofinal finite principal covers. It then constructs short
exact original Cech complexes and propagates all-positive principal-basis
Cech exactness through the actual successive injective-resolution kernels.
Those kernels are not assumed quasicoherent. The quasicoherent seed on
each principal open is proved by actual geometric restriction to its
localization scheme and the established affine Cech exactness theorem.

There are no domain, noetherianity, nontrivial-ring, flasque, or additional
acyclicity assumptions. This proves higher derived-global-section vanishing;
full faithfulness and essential image of the affine derived comparison are
separate results.

References: Stacks Project, [Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
and [Tag 01X9](https://stacks.math.columbia.edu/tag/01X9).
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped Simplicial
open PrimeSpectrum CategoryTheory.Cech
namespace AlgebraicGeometry.Scheme.Modules.AffineCech
variable {R : CommRingCat.{u}}

theorem exists_section_lift_of_cechOne_exact {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) {ι : Type u} (U : ι → (Spec R).Opens) (W : (Spec R).Opens)
    (hcover : iSup U = W)
    (hex : ((cechComplexFunctor U).obj (modulesSpecToSheaf.obj S.X₁).obj).ExactAt 1)
    (z : Section S.X₃ W) (s : ∀ i, Section S.X₂ (U i))
    (hs : ∀ i, mapSection S.g _ (s i) = res S.X₃ (hcover ▸ le_iSup U i) z) :
    ∃ t : Section S.X₂ W, mapSection S.g W t = z := by
  classical
  have hle (i : ι) : U i ≤ W := hcover ▸ le_iSup U i
  let := hS.mono_f
  have h (i j : ι) : ∃ c : Section S.X₁ (U i ⊓ U j),
      mapSection S.f _ c = res S.X₂ inf_le_left (s i) - res S.X₂ inf_le_right (s j) := by
    apply section_lift_of_shortExact hS
    simp only [map_sub, mapSection_res, hs, res_res, sub_self]
  choose c hc using h
  have hcoc (i j k : ι) :
      res S.X₁ (inf_le_left : (U i ⊓ U j) ⊓ U k ≤ _)
          (c i j) + res S.X₁ (inf_le_inf inf_le_right le_rfl) (c j k) =
        res S.X₁ (inf_le_inf inf_le_left le_rfl) (c i k) := by
    apply mapSection_injective S.f _
    simp only [map_add, mapSection_res, hc, map_sub, res_res]
    abel
  obtain ⟨b, hb⟩ := CategoryTheory.Cech.exists_cechOne_coboundary_of_exact
    U (modulesSpecToSheaf.obj S.X₁).obj hex c hcoc
  let t (i : ι) : Section S.X₂ (U i) := s i + mapSection S.f _ (b i)
  have ht (i j : ι) : res S.X₂
      (inf_le_left : U i ⊓ U j ≤ _) (t i) =
      res S.X₂ inf_le_right (t j) := by
    have h := congrArg (mapSection S.f (U i ⊓ U j)) (hb i j)
    simp only [map_sub, mapSection_res, hc] at h
    dsimp [t]
    simp only [map_add]
    exact (sub_eq_sub_iff_add_eq_add.mp h).symm.trans (add_comm _ _)
  obtain ⟨t', ht', _⟩ := TopCat.Sheaf.existsUnique_gluing' (modulesSpecToSheaf.obj S.X₂)
    U W (fun i => homOfLE (hle i)) (by rw [hcover]) t ht
  refine ⟨t', ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (modulesSpecToSheaf.obj S.X₃)
    U W (fun i => homOfLE (hle i)) (by rw [hcover])
  intro i
  change res S.X₃ (hle i) (mapSection S.g W t') = res S.X₃ (hle i) z
  rw [← mapSection_res]
  change mapSection S.g _ ((modulesSpecToSheaf.obj S.X₂).obj.map (homOfLE (hle i)).op t') = _
  rw [ht']
  simp only [t, map_add, mapSection_zero_comp, add_zero, hs]


lemma exists_finite_principal_section_lifts_on {M N : (Spec R).Modules}
    (q : M ⟶ N) [Epi q] (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (z : Section N W) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι → R)
      (hf : iSup (fun i => PrimeSpectrum.basicOpen (f i)) = W),
      ∃ s : ∀ i, Section M (PrimeSpectrum.basicOpen (f i)), ∀ i,
        mapSection q _ (s i) =
          res N (hf ▸ le_iSup (fun i => PrimeSpectrum.basicOpen (f i)) i) z := by
  classical
  have h (x : W) : ∃ r : R, x.val ∈ PrimeSpectrum.basicOpen r ∧
      ∃ hrW : PrimeSpectrum.basicOpen r ≤ W,
      ∃ s : Section M (PrimeSpectrum.basicOpen r), mapSection q _ s = res N hrW z := by
    let g := (_root_.PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map q.val
    have hg : TopCat.Presheaf.IsLocallySurjective g :=
      (inferInstance : _root_.PresheafOfModules.IsLocallySurjective
        (Opens.grothendieckTopology (Spec R)) q.val)
    obtain ⟨V, hV, ⟨s, hs⟩, hxV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff g).mp hg W z x.val x.property
    obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hxr, hrV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.isOpen
    refine ⟨r, hxr, hrV.trans hV, res M hrV s, ?_⟩
    change mapSection q V s = res N hV z at hs
    rw [mapSection_res, hs, res_res]
  choose f hf hfw s hs using h
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover
    (fun x : W => {y : Spec R | y ∈ PrimeSpectrum.basicOpen (f x)})
    (fun x => (PrimeSpectrum.basicOpen (f x)).isOpen)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hf ⟨x, hx⟩⟩)
  have hcover : (⨆ i : t, PrimeSpectrum.basicOpen (f i)) = W := by
    apply le_antisymm
    · exact iSup_le fun i => hfw i
    · intro x hx
      obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact Opens.mem_iSup.mpr ⟨⟨y, hyt⟩, hxy⟩
  exact ⟨t, inferInstance, fun i => f i, hcover, fun i => s i, fun i => hs i⟩

lemma sections_surjective_of_principalCech_exact_one
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (hex : ∀ (ι : Type u) [Fintype ι] (f : ι → R), (⨆ i, PrimeSpectrum.basicOpen (f i)) = W →
      ((cechComplexFunctor (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens))).obj
        (modulesSpecToSheaf.obj S.X₁).obj).ExactAt 1) :
    Function.Surjective (mapSection S.g W) := by
  let := hS.epi_g
  intro z
  obtain ⟨ι, hι, f, hf, s, hs⟩ := exists_finite_principal_section_lifts_on S.g W hW z
  let := hι
  exact exists_section_lift_of_cechOne_exact hS (fun i => PrimeSpectrum.basicOpen (f i)) W hf
    (hex ι f hf) z s hs

end AlgebraicGeometry.Scheme.Modules.AffineCech

namespace AlgebraicGeometry.Scheme.Modules.AffineCech

/-- The functor sending a module sheaf on `Spec R` to its presheaf of `R`-modules of sections, by
restricting scalars and forgetting the sheaf condition. -/
abbrev affineSectionPresheafFunctor (R : CommRingCat.{u}) :
    (Spec R).Modules ⥤ (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _

instance affineSectionPresheafFunctor_additive (R : CommRingCat.{u}) :
    (affineSectionPresheafFunctor R).Additive where
  map_add := by intros; rfl

lemma shortExact_sections_of_surjective {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) (W : (Spec R).Opens)
    (hs : Function.Surjective (mapSection S.g W)) :
    ((S.map (affineSectionPresheafFunctor R)).map
      ((evaluation _ _).obj (op W))).ShortExact := by
  let := hS.mono_f
  refine { exact := ?_
           mono_f := (ModuleCat.mono_iff_injective _).mpr (mapSection_injective S.f W)
           epi_g := (ModuleCat.epi_iff_surjective _).mpr hs }
  rw [ShortComplex.moduleCat_exact_iff]
  exact section_lift_of_shortExact hS W

lemma principalCech_shortExact_of_kernel_cechOne {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    (hK : ∀ (r : R) (ι : Type u) [Fintype ι] (f : ι → R),
      (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r →
        (principalCechComplex S.X₁ f).ExactAt 1)
    {ι : Type u} (f : ι → R) :
    ((S.map (affineSectionPresheafFunctor R)).map
      (cechComplexFunctor
        (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens)))).ShortExact := by
  apply cech_shortExact_of_sections
  intro n a
  rw [principal_product_eq]
  exact shortExact_sections_of_surjective hS _
    (sections_surjective_of_principalCech_exact_one hS _ (isCompact_basicOpen _)
      (hK (∏ i, f (a i))))

lemma principalCech_quotient_exact_succ {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) [Injective S.X₂]
    (hK : ∀ (r : R) (ι : Type u) [Fintype ι] (f : ι → R),
      (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r →
        ∀ n : ℕ, (principalCechComplex S.X₁ f).ExactAt (n + 1))
    (r : R) {ι : Type u} [Finite ι] (f : ι → R)
    (hf : (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r) (n : ℕ) :
    (principalCechComplex S.X₃ f).ExactAt (n + 1) := by
  let : Fintype ι := Fintype.ofFinite ι
  let T := (S.map (affineSectionPresheafFunctor R)).map
    (cechComplexFunctor (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec R).Opens)))
  have hT : T.ShortExact := principalCech_shortExact_of_kernel_cechOne hS
    (fun r ι _ f hf => hK r ι f hf 0) f
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₃ (n + 1) (n + 2) rfl).isZero_of_both_isZero
    (affine_injectiveCech_exact_succ S.X₂
      (fun i => PrimeSpectrum.basicOpen (f i)) n).isZero_homology
    (hK r ι f hf (n + 1)).isZero_homology

lemma injectiveResolution_kernel_principalCech_exact_succ {R : CommRingCat.{u}}
    (M : (Spec R).Modules)
    (hM : ∀ (r : R) (ι : Type u) [Fintype ι] (f : ι → R),
      (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r →
        ∀ n : ℕ, (principalCechComplex M f).ExactAt (n + 1))
    (I : CategoryTheory.InjectiveResolution M) (m : ℕ) :
    ∀ (r : R) (ι : Type u) [Finite ι] (f : ι → R),
      (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r → ∀ n : ℕ,
        (principalCechComplex (kernel (I.cocomplex.d (m + 1) (m + 2))) f).ExactAt (n + 1) := by
  induction m with
  | zero =>
    let : Injective (CategoryTheory.InjectiveResolution.initialSequence I).X₂ :=
      inferInstanceAs (Injective (I.cocomplex.X 0))
    intro r ι _ f hf n
    let : Fintype ι := Fintype.ofFinite ι
    exact principalCech_quotient_exact_succ
      (CategoryTheory.InjectiveResolution.initialSequence_shortExact I) hM r f hf n
  | succ m ih =>
    let : Injective (CategoryTheory.InjectiveResolution.kernelSequence I (m + 1)).X₂ :=
      inferInstanceAs (Injective (I.cocomplex.X (m + 1)))
    intro r ι _ f hf n
    let : Fintype ι := Fintype.ofFinite ι
    exact principalCech_quotient_exact_succ
      (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I (m + 1))
      (fun r ι _ f hf n => ih r ι f hf n) r f hf n

lemma globalSections_injectiveResolution_exact_succ_of_principalCech
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (hM : ∀ (r : R) (ι : Type u) [Fintype ι] (f : ι → R),
      (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r →
        ∀ n : ℕ, (principalCechComplex M f).ExactAt (n + 1))
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    ((moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) := by
  let C := I.cocomplex
  let k := kernel.lift (C.d (n + 1) (n + 2)) (C.d n (n + 1))
    (C.d_comp_d n (n + 1) (n + 2))
  have hk : Function.Surjective (moduleSpecΓFunctor.map k) := by
    cases n with
    | zero =>
      exact sections_surjective_of_principalCech_exact_one
        (CategoryTheory.InjectiveResolution.initialSequence_shortExact I) ⊤ isCompact_univ
        (fun ι _ f hf => hM 1 ι f (by simpa only [PrimeSpectrum.basicOpen_one] using hf) 0)
    | succ n =>
      exact sections_surjective_of_principalCech_exact_one
        (CategoryTheory.InjectiveResolution.kernelSequence_shortExact I (n + 1))
        ⊤ isCompact_univ
        (fun ι _ f hf => injectiveResolution_kernel_principalCech_exact_succ M hM I n
          1 ι f (by simpa only [PrimeSpectrum.basicOpen_one] using hf) 0)
  let K := ShortComplex.mk (kernel.ι (C.d (n + 1) (n + 2)))
    (C.d (n + 1) (n + 2)) (kernel.condition _)
  have hΓK : (K.map moduleSpecΓFunctor).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ (kernelIsKernel (C.d (n + 1) (n + 2))) moduleSpecΓFunctor)
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hΓK z hz
  obtain ⟨x, hx⟩ := hk y
  refine ⟨x, ?_⟩
  change moduleSpecΓFunctor.map (C.d n (n + 1)) x = z
  rw [← kernel.lift_ι (C.d (n + 1) (n + 2)) (C.d n (n + 1))
    (C.d_comp_d n (n + 1) (n + 2)), Functor.map_comp]
  change moduleSpecΓFunctor.map (kernel.ι (C.d (n + 1) (n + 2)))
    (moduleSpecΓFunctor.map k x) = z
  exact (congrArg (fun t => moduleSpecΓFunctor.map (kernel.ι (C.d (n + 1) (n + 2))) t) hx).trans hy

lemma isZero_rightDerived_globalSections_succ_of_principalCech
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (hM : ∀ (r : R) (ι : Type u) [Fintype ι] (f : ι → R),
      (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r →
        ∀ n : ℕ, (principalCechComplex M f).ExactAt (n + 1)) (n : ℕ) :
    IsZero ((moduleSpecΓFunctor.rightDerived (n + 1)).obj M) := by
  let I := injectiveResolution M
  exact (globalSections_injectiveResolution_exact_succ_of_principalCech M hM I
    n).isZero_homology.of_iso
    (I.isoRightDerivedObj moduleSpecΓFunctor (n + 1))

end AlgebraicGeometry.Scheme.Modules.AffineCech

namespace AlgebraicGeometry.Scheme.Modules.AffineCech

lemma principalCech_exactAt_succ_on_basicOpen {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (r : R)
    {ι : Type u} [Finite ι] (f : ι → R)
    (hf : (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r) (n : ℕ) :
    (principalCechComplex M f).ExactAt (n + 1) := by
  let A := CommRingCat.of (Localization.Away r)
  let a : R ⟶ A := CommRingCat.ofHom (algebraMap R _)
  let j : Spec A ⟶ Spec R := Spec.map a
  let M' := M.restrict j
  have hr : j.opensRange = PrimeSpectrum.basicOpen r := by simp [j, a, A]
  have hU (i : ι) : PrimeSpectrum.basicOpen (f i) ≤ j.opensRange := by
    rw [hr, ← hf]
    exact le_iSup (fun i => PrimeSpectrum.basicOpen (f i)) i
  have hcover : (⨆ i, PrimeSpectrum.basicOpen (a (f i))) = ⊤ := by
    simp only [← SpecMap_preimage_basicOpen]
    rw [← j.preimage_iSup, hf, ← hr, Scheme.Hom.preimage_opensRange]
  have h := principalCech_exactAt_succ M' (fun i => a (f i)) hcover n
  let F' := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  have hmap : ((F'.mapHomologicalComplex _).obj
      (principalCechComplex M' (fun i => a (f i)))).ExactAt (n + 1) := h.map F'
  have h' := hmap.of_iso
    (cechComplexCoefficientIso F' (fun i => PrimeSpectrum.basicOpen (a (f i)))
      (modulesSpecToSheaf.obj M').obj)
  have h'' : ((cechComplexFunctor (fun i => j ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))).obj
      M'.presheaf).ExactAt (n + 1) := by
    change ((cechComplexFunctor (fun i => PrimeSpectrum.basicOpen (a (f i)))).obj
      M'.presheaf).ExactAt (n + 1) at h'
    simpa only [j, SpecMap_preimage_basicOpen] using h'
  have hbase := h''.of_iso (cechRestrictIso j M (fun i => PrimeSpectrum.basicOpen (f i)) hU).symm
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  apply (ShortComplex.exact_map_iff_of_faithful _ F).mp
  exact hbase.of_iso
    (cechComplexCoefficientIso F (fun i => PrimeSpectrum.basicOpen (f i))
      (modulesSpecToSheaf.obj M).obj).symm

end AlgebraicGeometry.Scheme.Modules.AffineCech

namespace AlgebraicGeometry.Scheme.Modules.AffineDerived
open AffineCech

lemma globalSections_injectiveResolution_exact_succ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    ((moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) :=
  globalSections_injectiveResolution_exact_succ_of_principalCech M
    (fun r _ _ f hf n => principalCech_exactAt_succ_on_basicOpen M r f hf n) I n

lemma isZero_rightDerived_globalSections_succ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero ((moduleSpecΓFunctor.rightDerived (n + 1)).obj M) :=
  isZero_rightDerived_globalSections_succ_of_principalCech M
    (fun r _ _ f hf n => principalCech_exactAt_succ_on_basicOpen M r f hf n) n

end AlgebraicGeometry.Scheme.Modules.AffineDerived
