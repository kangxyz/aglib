/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.AffineDegreeOne
public import Aglib.AlgebraicGeometry.Modules.Epimorphisms
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Generators.LocalLifting
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
/-!
# Affine global sections with a quasicoherent kernel

For a short exact sequence of actual module sheaves on an arbitrary affine
scheme, `exists_global_section_lift` proves that every global quotient section
lifts if the kernel is quasicoherent. The middle and quotient sheaves are
unrestricted. The proof finds a finite principal cover with local lifts, solves
the resulting actual kernel-valued Cech cocycle, and glues corrected lifts.

`shortExact_globalSections_of_quasicoherent_kernel` expresses the conclusion
using the original `moduleSpecΓFunctor`. This is a degree-one geometric
acyclicity consequence, not exactness of global sections on arbitrary sheaves.
There are no noetherian, domain, or nontrivial-ring assumptions.

Reference: Stacks Project, [Tag 01EW](https://stacks.math.columbia.edu/tag/01EW).
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum

namespace AlgebraicGeometry.Scheme.Modules.AffineCech

variable {R : CommRingCat.{u}}

/-- The actual action of a sheaf morphism on sections, as an R-linear map. -/
abbrev mapSection {M N : (Spec R).Modules} (q : M ⟶ N) (U : (Spec R).Opens) :
    Section M U →ₗ[R] Section N U :=
  ((modulesSpecToSheaf.map q).hom.app (op U)).hom

lemma mapSection_res {M N : (Spec R).Modules} (q : M ⟶ N)
    {U V : (Spec R).Opens} (h : V ≤ U) (s : Section M U) :
    mapSection q V (res M h s) = res N h (mapSection q U s) :=
  ConcreteCategory.congr_hom ((modulesSpecToSheaf.map q).hom.naturality (homOfLE h).op) s

lemma mapSection_injective {M N : (Spec R).Modules} (q : M ⟶ N) [Mono q]
    (U : (Spec R).Opens) : Function.Injective (mapSection q U) :=
  (ModuleCat.mono_iff_injective
    ((SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)).map q)).mp inferInstance

/-- The kernel-exact part of a sheaf short exact sequence is exact on
sections over every open, without any quasicoherence assumption. -/
lemma section_lift_of_shortExact {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) (U : (Spec R).Opens) (s : Section S.X₂ U)
    (hs : mapSection S.g U s = 0) :
    ∃ t : Section S.X₁ U, mapSection S.f U t = s := by
  let F := SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf))
  let : PreservesFiniteColimits F := ⟨fun _ => inferInstance⟩
  have h := hS.map_of_exact F
  exact TopCat.Sheaf.sections_exact_of_left_exact (U := U) h.exact h.mono_f s hs

@[simp]
lemma mapSection_zero_comp (S : ShortComplex (Spec R).Modules)
    (U : (Spec R).Opens) (s : Section S.X₁ U) :
    mapSection S.g U (mapSection S.f U s) = 0 := by
  have h := congrArg (fun q => mapSection q U s) S.zero
  exact h

/-- A global section with lifts on a finite principal cover lifts globally
whenever the kernel of the sheaf short exact sequence is quasicoherent. The
middle and quotient sheaves need not be quasicoherent. -/
theorem exists_global_lift_of_principal_lifts {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] {ι : Type v} [Finite ι]
    (f : ι → R) (hcover : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤)
    (z : Section S.X₃ ⊤) (s : ∀ i, Section S.X₂ (PrimeSpectrum.basicOpen (f i)))
    (hs : ∀ i, mapSection S.g _ (s i) = res S.X₃ le_top z) :
    ∃ t : Section S.X₂ ⊤, mapSection S.g ⊤ t = z := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let := hS.mono_f
  have h (i j : ι) :
      ∃ c : Section S.X₁ (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)),
      mapSection S.f _ c = res S.X₂ inf_le_left (s i) - res S.X₂ inf_le_right (s j) := by
    apply section_lift_of_shortExact hS
    simp only [map_sub, mapSection_res, hs, res_res, sub_self]
  choose c hc using h
  have hcoc (i j k : ι) :
      res S.X₁ (inf_le_left : (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j)) ⊓
          PrimeSpectrum.basicOpen (f k) ≤ _)
          (c i j) + res S.X₁ (inf_le_inf inf_le_right le_rfl) (c j k) =
        res S.X₁ (inf_le_inf inf_le_left le_rfl) (c i k) := by
    apply mapSection_injective S.f _
    simp only [map_add, mapSection_res, hc, map_sub, res_res]
    abel
  obtain ⟨b, hb⟩ := exists_cechOne_coboundary S.X₁ f hcover c hcoc
  let t (i : ι) : Section S.X₂ (PrimeSpectrum.basicOpen (f i)) := s i + mapSection S.f _ (b i)
  have ht (i j : ι) : res S.X₂
      (inf_le_left : PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j) ≤ _) (t i) =
      res S.X₂ inf_le_right (t j) := by
    have h := congrArg
      (mapSection S.f (PrimeSpectrum.basicOpen (f i) ⊓ PrimeSpectrum.basicOpen (f j))) (hb i j)
    simp only [map_sub, mapSection_res, hc] at h
    dsimp [t]
    simp only [map_add]
    exact (sub_eq_sub_iff_add_eq_add.mp h).symm.trans (add_comm _ _)
  obtain ⟨t', ht', _⟩ := TopCat.Sheaf.existsUnique_gluing' (modulesSpecToSheaf.obj S.X₂)
    (fun i => PrimeSpectrum.basicOpen (f i)) ⊤ (fun i => homOfLE le_top) (by rw [hcover]) t ht
  refine ⟨t', ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (modulesSpecToSheaf.obj S.X₃)
    (fun i => PrimeSpectrum.basicOpen (f i)) ⊤ (fun i => homOfLE le_top) (by rw [hcover])
  intro i
  change res S.X₃ le_top (mapSection S.g ⊤ t') = res S.X₃ le_top z
  rw [← mapSection_res]
  change mapSection S.g _ ((modulesSpecToSheaf.obj S.X₂).obj.map (homOfLE le_top).op t') = _
  rw [ht']
  simp only [t, map_add, mapSection_zero_comp, add_zero, hs]

/-- A section over an affine scheme has lifts on some finite principal
cover under an arbitrary epimorphism of module sheaves. -/
lemma exists_finite_principal_section_lifts {M N : (Spec R).Modules}
    (q : M ⟶ N) [Epi q] (z : Section N ⊤) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι → R),
      (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤ ∧
      ∃ s : ∀ i, Section M (PrimeSpectrum.basicOpen (f i)), ∀ i,
        mapSection q _ (s i) = res N le_top z := by
  classical
  have h (x : Spec R) : ∃ r : R, x ∈ PrimeSpectrum.basicOpen r ∧
      ∃ s : Section M (PrimeSpectrum.basicOpen r), mapSection q _ s = res N le_top z := by
    let g := (_root_.PresheafOfModules.toPresheaf (Spec R).ringCatSheaf.obj).map q.val
    have hg : TopCat.Presheaf.IsLocallySurjective g :=
      (inferInstance : _root_.PresheafOfModules.IsLocallySurjective
        (Opens.grothendieckTopology (Spec R)) q.val)
    obtain ⟨U, hU, ⟨s, hs⟩, hxU⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff g).mp hg ⊤ z x (by trivial)
    obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hxr, hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    refine ⟨r, hxr, res M hrU s, ?_⟩
    change mapSection q U s = res N hU z at hs
    rw [mapSection_res, hs, res_res]
  choose f hf s hs using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : Spec R => {y : Spec R | y ∈ PrimeSpectrum.basicOpen (f x)})
    (fun x => (PrimeSpectrum.basicOpen (f x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hf x⟩)
  refine ⟨t, inferInstance, fun x => f x, ?_, fun x => s x, fun x => hs x⟩
  apply top_unique
  intro x _
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨y, hyt⟩, hxy⟩

/-- Affine global sections lift across a short exact sequence whenever its
kernel is quasicoherent. No quasicoherence of the middle or quotient sheaf is
assumed. This is the geometric degree-one acyclicity consequence of the
finite principal-cover Cech calculation. -/
theorem exists_global_section_lift {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] (z : Section S.X₃ ⊤) :
    ∃ t : Section S.X₂ ⊤, mapSection S.g ⊤ t = z := by
  let := hS.epi_g
  obtain ⟨ι, hι, f, hcover, s, hs⟩ := exists_finite_principal_section_lifts S.g z
  let := hι
  exact exists_global_lift_of_principal_lifts hS f hcover z s hs

/-- The actual affine global-sections map of the quotient is an epimorphism
for every short exact sequence with quasicoherent kernel. -/
theorem epi_globalSections_of_quasicoherent_kernel {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    Epi (moduleSpecΓFunctor.map S.g) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact exists_global_section_lift hS

/-- Actual affine global sections are right adjoint to associated sheaves. -/
instance globalSections_isRightAdjoint (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint

/-- Actual affine global sections preserve a short exact sequence if its
kernel is quasicoherent. This does not assert exactness on all sheaves. -/
theorem shortExact_globalSections_of_quasicoherent_kernel
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    (S.map moduleSpecΓFunctor).ShortExact := by
  let := hS.mono_f
  refine { exact := ?_
           mono_f := ?_
           epi_g := epi_globalSections_of_quasicoherent_kernel hS }
  · rw [ShortComplex.moduleCat_exact_iff]
    exact fun s hs => section_lift_of_shortExact hS ⊤ s hs
  · change Mono (moduleSpecΓFunctor.map S.f)
    infer_instance

end AlgebraicGeometry.Scheme.Modules.AffineCech
