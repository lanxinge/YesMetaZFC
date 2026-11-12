import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.Model.SetTheory.Relations.Separation
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.Model.SetTheory.Internal.TruthImage
import YesMetaZFC.Model.SetTheory.Embedding.Reflect
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.Collection
import YesMetaZFC.Model.SetTheory.Source.Theory
import YesMetaZFC.SetTheory.InaccessibleHierarchy
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.Model.SetTheory.Source.BinaryRelation
import YesMetaZFC.Model.SetTheory.Source.CollectionBasis
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Internal.Extensionality

/-! # 背景内部的完整 ZFC 模型证书

固定公理与两个模式均由一个背景公式读取。模式量化全部内部程序和赋值，
不把外部标准 AST 的逐条满足误作内部 ZFC。收集只断言存在集合界，尚未选择函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def zc_base_m : Formula 1 0 :=
  .conj Axioms.extensionality.formula (.conj Axioms.emptySet.formula
    (.conj Axioms.pairing.formula (.conj Axioms.union.formula
      (.conj Axioms.powerSet.formula (.conj Axioms.infinity.formula
        (.conj Axioms.foundation.formula Axioms.choice.formula))))))

theorem zc_base_closed_l : zc_base_m.FreeClosed :=
  ⟨Axioms.extensionality.freeClosed, Axioms.emptySet.freeClosed, Axioms.pairing.freeClosed,
    Axioms.union.freeClosed, Axioms.powerSet.freeClosed, Axioms.infinity.freeClosed,
    Axioms.foundation.freeClosed, Axioms.choice.freeClosed⟩

structure Zc_schemas_d (ω X R : M.Domain) : Prop where
  separation : ∀ E F n r i f D, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem f E → M.mem D X → ∃ A, M.mem A X ∧ Sr_sep_d I X R E F n r i f D A
  collection : ∀ E F n r i j f D, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem j ω → i ≠ j → M.mem f E → M.mem D X →
    (∀ x, M.mem x X → M.PairMember I x D R → ∃ y, M.mem y X ∧ Sbin_d I X R E F n r i j f x y) →
    ∃ C, M.mem C X ∧ ∀ x, M.mem x X → M.PairMember I x D R →
      ∃ y, M.mem y X ∧ M.PairMember I y C R ∧ Sbin_d I X R E F n r i j f x y

structure Zc_model_d (ω c X R : M.Domain) : Prop where
  model : Smdl_d I c X R
  ext : Rf_ext_d I X R
  base : ∀ ρ : Env (smdl_structure_l I (R := R) model.2.1) 0, Formula.satisfies ρ zc_base_m
  schemas : Zc_schemas_d I ω X R

@[simp] private theorem zc_space_closed_l {d} (E ω X : Term d)
    (he : E.freeSupport = []) (hw : ω.freeSupport = []) (hx : X.freeSupport = []) :
    (Formula.isFunctionSpace kpair_convention_l E ω X).FreeClosed := by
  simp -implicitDefEqProofs [Formula.isFunctionSpace, Definitional.Formula.FreeClosed, he, hw, hx]

def zc_separation_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪
  ∀ E F n r i f D,
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, ⌜X⌝ₛ) →
    ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, n, F) →
    r ∈ n → i ∈ ⌜ω⌝ₛ → f ∈ E → D ∈ ⌜X⌝ₛ → ∃ A ∈ ⌜X⌝ₛ,
      ∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, A, ⌜R⌝ₛ) ↔
        ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, D, ⌜R⌝ₛ) ∧ (∃ g,
          ⌜senv_update_m (𝒞 := kpair_convention_l)⌝ₚ(f, i, x, g) ∧
          ⌜ssat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, g))⟫
derive_free_closed zc_separation_m

def zc_collection_m {d} (ω X R : Term d) : Formula 1 d := set[d] ⟪
  ∀ E F n r i j f D,
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, ⌜X⌝ₛ) →
    ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, n, F) →
    r ∈ n → i ∈ ⌜ω⌝ₛ → j ∈ ⌜ω⌝ₛ → i ≠ j → f ∈ E → D ∈ ⌜X⌝ₛ →
    (∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, D, ⌜R⌝ₛ) → ∃ y ∈ ⌜X⌝ₛ,
      ⌜sbin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, i, j, f, x, y)) →
    ∃ C ∈ ⌜X⌝ₛ, ∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, D, ⌜R⌝ₛ) →
      ∃ y ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(y, C, ⌜R⌝ₛ) ∧
        ⌜sbin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, E, F, n, r, i, j, f, x, y)⟫
derive_free_closed zc_collection_m

def zc_model_m {d} (ω c X R : Term d) : Formula 1 d :=
  .conj (smdl_m (𝒞 := kpair_convention_l) c X R)
    (.conj (rf_ext_m (𝒞 := kpair_convention_l) X R)
      (.conj (rr_rel_m kpair_convention_l zc_base_m X R Fin.elim0)
        (.conj (zc_separation_m ω X R) (zc_collection_m ω X R))))

@[simp] theorem zc_model_closed_l {d} (ω c X R : Term d) (hω : ω.freeSupport = [])
    (hc : c.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = []) :
    (zc_model_m ω c X R).FreeClosed := by
  simp only [zc_model_m, Definitional.Formula.FreeClosed]
  exact ⟨smdl_m_freeClosed c X R hc hX hR, rf_ext_m_freeClosed X R hX hR,
    rr_rel_closed_l _ _ zc_base_closed_l X R Fin.elim0 hX hR (fun i => Fin.elim0 i),
    zc_separation_m_freeClosed ω X R hω hX hR, zc_collection_m_freeClosed ω X R hω hX hR⟩

/-- 解码保留内部非标准程序；没有额外的模型闭包前提。 -/
theorem zc_model_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X R : Term d) :
    Formula.satisfies ρ (zc_model_m ω c X R) ↔
      Zc_model_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (R.eval ρ) := by
  have sep : Formula.satisfies ρ (zc_separation_m ω X R) ↔
      ∀ E F n r i f D, M.IsFunctionSpace I E (ω.eval ρ) (X.eval ρ) → Sfm_d I (ω.eval ρ) n F →
        M.mem r n → M.mem i (ω.eval ρ) → M.mem f E → M.mem D (X.eval ρ) →
          ∃ A, M.mem A (X.eval ρ) ∧ Sr_sep_d I (X.eval ρ) (R.eval ρ) E F n r i f D A := by
    simp only [zc_separation_m, Sr_sep_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isFunctionSpace_iff I hE,
      sfm_sat_l I hE, senv_update_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl
  have collect : Formula.satisfies ρ (zc_collection_m ω X R) ↔
      ∀ E F n r i j f D, M.IsFunctionSpace I E (ω.eval ρ) (X.eval ρ) → Sfm_d I (ω.eval ρ) n F →
        M.mem r n → M.mem i (ω.eval ρ) → M.mem j (ω.eval ρ) → i ≠ j → M.mem f E → M.mem D (X.eval ρ) →
        (∀ x, M.mem x (X.eval ρ) → M.PairMember I x D (R.eval ρ) →
          ∃ y, M.mem y (X.eval ρ) ∧ Sbin_d I (X.eval ρ) (R.eval ρ) E F n r i j f x y) →
        ∃ C, M.mem C (X.eval ρ) ∧ ∀ x, M.mem x (X.eval ρ) → M.PairMember I x D (R.eval ρ) →
          ∃ y, M.mem y (X.eval ρ) ∧ M.PairMember I y C (R.eval ρ) ∧
            Sbin_d I (X.eval ρ) (R.eval ρ) E F n r i j f x y := by
    simp only [zc_collection_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_orderedPairMem_iff I,
      Formula.satisfies_isFunctionSpace_iff I hE, sfm_sat_l I hE, sbin_sat_l I hE,
      Formula.extensionalNe, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
      Definitional.Term.eval_weaken]; rfl
  simp only [zc_model_m, Formula.satisfies_conj_iff, smdl_sat_l I, rf_ext_sat_l I hE, sep, collect]
  constructor
  · rintro ⟨hm, ext, base, hs, hc⟩
    exact ⟨hm, ext, fun η => (rr_rel_sat_l I hm.2.1 _ zc_base_closed_l η ρ X R Fin.elim0
      rfl rfl (fun i => Fin.elim0 i)).mp base, hs, hc⟩
  · intro h
    obtain ⟨x, hx⟩ := h.model.2.1
    let η : Env (smdl_structure_l I (R := R.eval ρ) h.model.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
    exact ⟨h.model, h.ext, (rr_rel_sat_l I h.model.2.1 _ zc_base_closed_l η ρ X R Fin.elim0
      rfl rfl (fun i => Fin.elim0 i)).mpr (h.base η), h.schemas.separation, h.schemas.collection⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整内部 ZFC 证书向成员满外层的保持

目标中的任意内部程序回拉为源程序，任意完整赋值在该程序的有限支撑上回拉。
分离集与收集界由源证书实际给出；两个模式仍覆盖目标的全部程序和全部赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (e : M.Domain → N.Domain)
  (inj : Function.Injective e) (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
  (hM : M.Models ZF) (hN : N.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full hM hN

theorem image_zc_schemas_l {ω X R : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (ne : ∃ x, M.mem x X) (h : Zc_schemas_d I ω X R) : Zc_schemas_d J (e ω) (e X) (e R) := by
  have mem {a b : M.Domain} : N.mem (e a) (e b) ↔ M.mem a b := image_member_l e inj full
  have entry := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  obtain ⟨E,space⟩ := ZF.exists_functionSpace hM I ω X
  constructor
  · intro K F n r i g D space' program' hr' hi' hg hD'
    obtain ⟨n,F,program,rfl,rfl⟩ := image_sfm_pull_l e inj full hM hN hw hw' program'
    obtain ⟨r,hr,rfl⟩ := (full n r).mp hr'
    obtain ⟨i,hi,rfl⟩ := (full ω i).mp hi'
    obtain ⟨D,hD,rfl⟩ := (full X D).mp hD'
    obtain ⟨b,hb,bound⟩ := sbound_exists_l I hM hw program
    obtain ⟨f,fn,agree⟩ := image_assignment_l e inj full hM hN hw hw' hb ne ((space' g).mp hg)
    have hf := (space f).mpr fn
    have hf' := (space' (e f)).mpr
      (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full fn)
    obtain ⟨A,hA,sep⟩ := h.separation E F n r i f D space program hr hi hf hD
    refine ⟨e A,mem.mpr hA,(sr_sep_agree_l J hN program'
      (image_sbound_l e inj full hM hN hw' program hb bound) hr' hi' space' hg hf' agree).mpr ?_⟩
    intro x hx
    obtain ⟨x,hx₀,rfl⟩ := (full X x).mp hx
    exact (entry x A R).symm.trans ((sep x hx₀).trans (and_congr (entry x D R)
      (image_unary_truth_l e inj full hM hN hw hw' program hr space space' hf hi hx₀)))
  · intro K F n r i j g D space' program' hr' hi' hj' hij hg hD' total
    obtain ⟨n,F,program,rfl,rfl⟩ := image_sfm_pull_l e inj full hM hN hw hw' program'
    obtain ⟨r,hr,rfl⟩ := (full n r).mp hr'
    obtain ⟨i,hi,rfl⟩ := (full ω i).mp hi'
    obtain ⟨j,hj,rfl⟩ := (full ω j).mp hj'
    obtain ⟨D,hD,rfl⟩ := (full X D).mp hD'
    obtain ⟨b,hb,bound⟩ := sbound_exists_l I hM hw program
    obtain ⟨f,fn,agree⟩ := image_assignment_l e inj full hM hN hw hw' hb ne ((space' g).mp hg)
    have hf := (space f).mpr fn
    have hf' := (space' (e f)).mpr
      (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e inj full fn)
    have truth x y (hx : M.mem x X) (hy : M.mem y X) :
        Sbin_d I X R E F n r i j f x y ↔ Sbin_d J (e X) (e R) K (e F) (e n) (e r) (e i) (e j) g (e x) (e y) :=
      (image_sbin_l e inj full hM hN hw hw' program hr space space' hf hi hj hx hy).trans
        (sbin_agree_l J hN program' (image_sbound_l e inj full hM hN hw' program hb bound)
          hr' hi' hj' space' hg hf' agree (mem.mpr hx) (mem.mpr hy)).symm
    have total' x (hx : M.mem x X) (hd : M.PairMember I x D R) :
        ∃ y, M.mem y X ∧ Sbin_d I X R E F n r i j f x y := by
      obtain ⟨y,hy,ht⟩ := total (e x) (mem.mpr hx) ((entry x D R).mp hd)
      obtain ⟨y,hy₀,rfl⟩ := (full X y).mp hy
      exact ⟨y,hy₀,(truth x y hx hy₀).mpr ht⟩
    obtain ⟨C,hC,collect⟩ := h.collection E F n r i j f D space program hr hi hj
      (fun eq => hij (congrArg e eq)) hf hD total'
    refine ⟨e C,mem.mpr hC,fun x hx hd => ?_⟩
    obtain ⟨x,hx₀,rfl⟩ := (full X x).mp hx
    obtain ⟨y,hy,hc,ht⟩ := collect x hx₀ ((entry x D R).mpr hd)
    exact ⟨e y,mem.mpr hy,(entry y C R).mp hc,(truth x y hx₀ hy).mp ht⟩

/-- 保持的是完整内部证书，而不只是外部标准句子的逐条满足。 -/
theorem image_zc_model_l {ω c X R : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (h : Zc_model_d I ω c X R) : Zc_model_d J (e ω) (e c) (e X) (e R) := by
  have model := image_smdl_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) h.model
  have entry := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  refine ⟨model,?_,?_,image_zc_schemas_l e inj full hM hN hw hw' h.model.2.1 h.schemas⟩
  · intro x hx y hy same
    obtain ⟨a,ha,rfl⟩ := (full X x).mp hx
    obtain ⟨b,hb,rfl⟩ := (full X y).mp hy
    exact congrArg e (h.ext a ha b hb (fun z hz => (entry z a R).trans
      ((same (e z) ((image_member_l e inj full).mpr hz)).trans (entry z b R).symm)))
  · let φ : Sentence := ⟨zc_base_m,zc_base_closed_l⟩
    have base : (smdl_structure_l I (R := R) h.model.2.1).Models (fun ψ => ψ = φ) := by
      refine ⟨h.ext.native_l I h.model.2.1,fun ψ eq => ?_⟩
      subst ψ
      rw [Structure.satisfiesSentence_iff]
      exact fun g => h.base ⟨Fin.elim0,g⟩
    have moved := image_smdl_models_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN) h.model base
    intro η
    exact (Structure.satisfiesSentence_iff _ φ).mp (moved.2 φ rfl) η.free

end YesMetaZFC.SetTheory.Internal

/-! ## 内部 ZFC 证书的原语言解码

把任意原模式编成实际程序，在同一原关系载体内改写实参槽位，再读取内部模式。
此处没有传递性、外部序列闭性或传递坍塌假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hZF : M.Models ZF)
  {ω c X R : M.Domain}
include hZF

theorem Zc_model_d.separate_l (hω : M.IsOmega ω) (h : Zc_model_d I ω c X R)
    {p} (φ : UnarySchema p) (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) p)
    (D : (smdl_structure_l I (R := R) h.model.2.1).Domain) :
    ∃ A : (smdl_structure_l I (R := R) h.model.2.1).Domain, ∀ x,
      M.PairMember I x.val A.val R ↔ M.PairMember I x.val D.val R ∧ φ.denote ρ x := by
  obtain ⟨a, n, F, r, v, hF, hv, code⟩ := source_compile_l I hZF hω φ.body φ.freeClosed
  have inj : Function.Injective v := fun i j e => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (e.symm ▸ hv j))
  have vn i := num_mem_l hZF.1 hω (hv i)
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨f, hf, params⟩ := senv_params_l I hZF hE h.model.2.1 v
    (fun i => ((ρ.push D).bound i).val) inj vn (fun i => ((ρ.push D).bound i).property)
  have read x g (hu : Senv_update_d I f (v 0) x.val g) :
      Ssat_d I X R E F n r g ↔ φ.denote ρ x := by
    apply code X R h.model.2.1 E hE g
      ((hE g).mpr (hu.function_l I ((hE f).mp hf) (vn 0) x.property)) (ρ.push x)
    exact Fin.cases ((hu.2 (v 0) x.val).mpr (Or.inl ⟨rfl, rfl⟩)) (fun i =>
      (hu.2 (v i.succ) (ρ.bound i).val).mpr
        (Or.inr ⟨fun e => Fin.succ_ne_zero i (inj e), params i.succ⟩))
  obtain ⟨A, hA, sep⟩ := h.schemas.separation E F n r (v 0) f D.val hE hF.2.1 hF.2.2 (vn 0) hf D.property
  refine ⟨⟨A, hA⟩, fun x => (sep x.val x.property).trans (and_congr_right fun _ => ?_)⟩
  refine ⟨fun ⟨g, hu, ht⟩ => (read x g hu).mp ht, fun ht => ?_⟩
  obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (vn 0) x.property
  exact ⟨g, hu, (read x g hu).mpr ht⟩

theorem Zc_model_d.collect_l (hω : M.IsOmega ω) (h : Zc_model_d I ω c X R)
    {p} (φ : BinarySchema p) (ρ : Env (smdl_structure_l I (R := R) h.model.2.1) p)
    (D : (smdl_structure_l I (R := R) h.model.2.1).Domain)
    (total : ∀ x, M.PairMember I x.val D.val R → ∃ y, φ.denote ρ x y) :
    ∃ C : (smdl_structure_l I (R := R) h.model.2.1).Domain, ∀ x,
      M.PairMember I x.val D.val R → ∃ y, M.PairMember I y.val C.val R ∧ φ.denote ρ x y := by
  obtain ⟨a, n, F, r, v, hF, hv, code⟩ := source_compile_l I hZF hω φ.body φ.freeClosed
  have inj : Function.Injective v := fun i j e => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (e.symm ▸ hv j))
  have vn i := num_mem_l hZF.1 hω (hv i)
  have ne : v 1 ≠ v 0 := fun e => by have q := congrArg Fin.val (inj e); simp at q
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨f, hf, params⟩ := senv_params_l I hZF hE h.model.2.1 v
    (fun i => (((ρ.push D).push D).bound i).val) inj vn (fun i => (((ρ.push D).push D).bound i).property)
  have read (x y : (smdl_structure_l I (R := R) h.model.2.1).Domain) :
      Sbin_d I X R E F n r (v 1) (v 0) f x.val y.val ↔ φ.denote ρ x y := by
    obtain ⟨g, hu, fg⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (vn 1) x.property
    obtain ⟨t, ht, ft⟩ := senv_update_exists_l I hZF fg (vn 0) y.property
    apply (sbin_value_l I hZF.1 hu ht).trans
    apply code X R h.model.2.1 E hE t ((hE t).mpr ft) ((ρ.push x).push y)
    refine Fin.cases ((ht.2 (v 0) y.val).mpr (Or.inl ⟨rfl, rfl⟩)) (Fin.cases
      ((ht.2 (v 1) x.val).mpr (Or.inr ⟨ne, (hu.2 (v 1) x.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)) ?_)
    intro i
    exact (ht.2 (v i.succ.succ) (ρ.bound i).val).mpr (Or.inr
      ⟨fun e => Fin.succ_ne_zero i.succ (inj e), (hu.2 (v i.succ.succ) (ρ.bound i).val).mpr
        (Or.inr ⟨fun e => Fin.succ_ne_zero i (Fin.succ_inj.mp (inj e)), params i.succ.succ⟩)⟩)
  obtain ⟨C, hC, bound⟩ := h.schemas.collection E F n r (v 1) (v 0) f D.val hE hF.2.1 hF.2.2
    (vn 1) (vn 0) ne hf D.property (fun x hx hd => by
      obtain ⟨y, hy⟩ := total ⟨x, hx⟩ hd
      exact ⟨y.val, y.property, (read ⟨x, hx⟩ y).mpr hy⟩)
  refine ⟨⟨C, hC⟩, fun x hx => ?_⟩
  obtain ⟨y, hy, hc, hs⟩ := bound x.val x.property hx
  exact ⟨⟨y, hy⟩, hc, (read x ⟨y, hy⟩).mp hs⟩

/-- 外部标准公理只是内部证书的解码后果，不能反过来代替内部模式。 -/
theorem Zc_model_d.native_l (hω : M.IsOmega ω) (h : Zc_model_d I ω c X R) :
    (smdl_structure_l I (R := R) h.model.2.1).Models ZFC := by
  refine ⟨h.ext.native_l I h.model.2.1, fun s hs => ?_⟩
  rw [Structure.satisfiesSentence_iff]
  intro f
  have hb := h.base ⟨Fin.elim0, f⟩
  simp only [zc_base_m, Formula.satisfies_conj_iff] at hb
  cases hs with
  | choice => exact hb.2.2.2.2.2.2.2
  | zf hs =>
    cases hs with
    | extensionality => exact hb.1
    | emptySet => exact hb.2.1
    | pairing => exact hb.2.2.1
    | union => exact hb.2.2.2.1
    | powerSet => exact hb.2.2.2.2.1
    | infinity => exact hb.2.2.2.2.2.1
    | foundation => exact hb.2.2.2.2.2.2.1
    | separation φ =>
      apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.separationCore φ)).mpr
      intro b
      exact (Axioms.Schema.separation_sat_iff_d ⟨b, f⟩ φ).mpr (h.separate_l I hZF hω φ ⟨b, f⟩)
    | collection φ =>
      apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.collectionCore φ)).mpr
      intro b
      exact (Axioms.Schema.collection_sat_iff_d ⟨b, f⟩ φ).mpr (h.collect_l I hZF hω φ ⟨b, f⟩)

theorem Zc_model_d.membership_l (hω : M.IsOmega ω) (h : Zc_model_d I ω c X R)
    (hm : Smem_d I c X R) (nx : Nonempty {x // M.mem x X}) : (rt_model_l X nx).Models ZFC := by
  have native := h.native_l I hZF hω
  refine ⟨?_, fun s hs => ?_⟩
  · refine ⟨fun x y same => native.1.eq_of_same_members x y (fun z => ?_)⟩
    exact ((hm.2 z.val x.val).trans ⟨fun e => e.2.2, fun e => ⟨z.property, x.property, e⟩⟩).trans
      ((same z).trans ((hm.2 z.val y.val).trans ⟨fun e => e.2.2, fun e => ⟨z.property, y.property, e⟩⟩).symm)
  · rw [Structure.satisfiesSentence_iff]
    intro f
    exact (smem_formula_l I hm nx s.formula ⟨Fin.elim0, f⟩).mpr
      ((Structure.satisfiesSentence_iff ..).mp (native.2 s hs) f)

end YesMetaZFC.SetTheory.Internal

/-! ## 不可达秩段上的实际内部 ZFC 证书

固定公理由秩闭包验证。不可达性给出 Vδ = Hδ，全部内部收集实例因此拥有
实际集合界；不使用外部可数闭性，也不以待证证书作为实例前提。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem zc_v_base_l {ω δ X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (above : M.mem ω δ) (rank : V_d I δ X) (nx : Nonempty {x // M.mem x X})
    (ρ : Env (rt_model_l X nx) 0) : Formula.satisfies ρ zc_base_m := by
  have tr := v_transitive_l I rank
  have ext := rt_model_ext_l hZF.1 tr nx
  have alg := sc_v_algebra_l hZFC hδ rank
  have same (x y : (rt_model_l X nx).Domain) : (rt_model_l X nx).SameMembers x y ↔ x.val = y.val :=
    ⟨fun h => congrArg Subtype.val (ext.eq_of_same_members x y h), fun h => (Subtype.ext h : x = y) ▸ fun _ => Iff.rfl⟩
  simp only [zc_base_m, Formula.satisfies_conj_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Axioms.extensionality, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq ext]
    exact ext.eq_of_same_members
  · obtain ⟨e, he, heω⟩ := hω.1.1
    exact (Axioms.satisfies_emptySet_iff ρ.free).mpr
      ⟨⟨e, tr ω (ZF.v_ordinal_mem_l I hZF rank above) e heω⟩, fun z => he z.val⟩
  · apply (Axioms.satisfies_pairing_iff ρ.free).mpr
    intro a b
    obtain ⟨p, hp, pair⟩ := alg.pair a.val b.val a.property b.property
    exact ⟨⟨p, hp⟩, fun z => (pair z.val).trans (or_congr (same z a).symm (same z b).symm)⟩
  · apply (Axioms.satisfies_union_iff ρ.free).mpr
    intro A
    obtain ⟨U, hu, un⟩ := alg.union A.val A.property
    exact ⟨⟨U, hu⟩, fun z => (un z.val).trans
      ⟨fun ⟨a, ha, hz⟩ => ⟨⟨a, tr A.val A.property a ha⟩, ha, hz⟩, fun ⟨a, ha, hz⟩ => ⟨a.val, ha, hz⟩⟩⟩
  · apply (Axioms.satisfies_powerSet_iff ρ.free).mpr
    intro A
    obtain ⟨P, power⟩ := ZF.exists_powerSet hZF A.val
    exact ⟨⟨P, v_power_mem_l I rank hδ A.property power⟩, fun z => (power z.val).trans
      ⟨fun sub y hy => sub y.val hy, fun sub y hy => sub ⟨y, tr z.val z.property y hy⟩ hy⟩⟩
  · apply (Axioms.satisfies_infinity_iff ρ.free).mpr
    have hwX := ZF.v_ordinal_mem_l I hZF rank above
    refine ⟨⟨ω, hwX⟩, ?_, fun a ha => ?_⟩
    · obtain ⟨e, he, heω⟩ := hω.1.1
      exact ⟨⟨e, tr ω hwX e heω⟩, fun z => he z.val, heω⟩
    · obtain ⟨s, hs, hsω⟩ := hω.1.2 a.val ha
      exact ⟨⟨s, tr ω hwX s hsω⟩, fun z => (hs z.val).trans (or_congr_right
        ⟨fun h v => h v.val, fun h => (same z a).mp h ▸ fun _ => Iff.rfl⟩), hsω⟩
  · apply (Axioms.foundation_sat_iff_d ρ.free).mpr
    intro A hn
    obtain ⟨z, hz⟩ := hn
    obtain ⟨a, ha, minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ⟨z.val, hz⟩
    exact ⟨⟨a, tr A.val A.property a ha⟩, ha, fun y hy => minimal y.val hy⟩
  · simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, Formula.extensionalNe, Formula.satisfies_neg_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq ext,
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    intro A hn
    obtain ⟨C, select⟩ := ZFC.choice_set_l hZFC A.val (fun a ha =>
      (hn.1 ⟨a, tr A.val A.property a ha⟩ ha).elim fun x hx => ⟨x.val, hx⟩) (by
        intro a ha b hb ne ⟨x, hx, hy⟩
        exact hn.2 ⟨a, tr A.val A.property a ha⟩ ha ⟨b, tr A.val A.property b hb⟩ hb
          (fun e => ne (congrArg Subtype.val e)) ⟨⟨x, tr a (tr A.val A.property a ha) x hx⟩, hx, hy⟩)
    -- 选择集先截到族的并集，故所得实际对象仍属于原秩段。
    obtain ⟨U, hu, un⟩ := alg.union A.val A.property
    let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
    obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF φ ⟨fun _ => C, fun _ => C⟩ U
    have spec x : M.mem x B ↔ M.mem x U ∧ M.mem x C := hb x
    refine ⟨⟨B, v_subset_mem_l I rank hu (fun x hx => ((spec x).mp hx).1)⟩, fun a ha => ?_⟩
    obtain ⟨x, hx, unique⟩ := select a.val ha
    exact ⟨⟨x, tr a.val a.property x hx.2⟩, ⟨(spec x).mpr ⟨(un x).mpr ⟨a.val, ha, hx.2⟩, hx.1⟩, hx.2⟩,
      fun y hy => Subtype.ext (unique y.val ⟨((spec y.val).mp hy.1).2, hy.2⟩)⟩

/-- 载体、隶属图和全部公理实例同时产生，不从证书前提取出另一份证书。 -/
theorem zc_inaccessible_l {ω δ X : M.Domain} (hω : M.IsOmega ω) (above : M.mem ω δ)
    (regular : M.IsRegularCardinal I δ) (strong : M.IsStrongLimitCardinal I δ) (rank : V_d I δ X) :
    ∃ c R, Smem_d I c X R ∧ Zc_model_d I ω c X R := by
  have tr := v_transitive_l I rank
  have hwX := ZF.v_ordinal_mem_l I hZF rank above
  obtain ⟨c, R, hm⟩ := smdl_membership_l I hZF ⟨ω, hwX⟩
  have mem x y (hx : M.mem x X) (hy : M.mem y X) : M.PairMember I x y R ↔ M.mem x y :=
    (hm.2 x y).trans ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩
  have hereditary := ZFC.inaccessible_hereditary_l I hZFC hω above regular strong rank
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hwX⟩⟩
  refine ⟨c, R, hm, hm.1, rf_ext_mem_l I hZF.1 tr hm, ?_, ?_, ?_⟩
  · intro ρ
    exact (smem_formula_l I hm nx zc_base_m ⟨ρ.bound, ρ.free⟩).mp
      (zc_v_base_l hZFC hω regular.isLimitOrdinal above rank nx ⟨ρ.bound, ρ.free⟩)
  · intro E F n r i f D hE hF hr hi hf hD
    obtain ⟨A, hA, sep⟩ := (sc_v_theory_l hZFC regular.isLimitOrdinal rank ω R hm).separation
      E F n r i f D hE hF hr hi hf hD
    exact ⟨A,hA,sep⟩
  · intro E F n r i j f D _ _ _ _ _ _ _ hD total
    obtain ⟨C, q, hC, fn, select⟩ := h_collect_function_l I hZFC hω regular above hereditary hD
      (fun x hx => total x (tr D hD x hx) ((mem x D (tr D hD x hx) hD).mpr hx))
    refine ⟨C, hC, fun x hx hd => ?_⟩
    obtain ⟨y, hy, hxy⟩ := fn.2.2 x ((mem x D hx hD).mp hd)
    exact ⟨y, tr C hC y hy, (mem y C (tr C hC y hy) hC).mpr hy, select x y hxy⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原秩段的关系收集界与弱背景中的模型构造

不可达秩段对小定义域总关系有实际层内见证界。这一条有限语句可随原一步规则
反射；在 KP 中，任意原公式的相对化都是 Δ₀，因而可直接读取分离与收集模式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_bound_d (X : M.Domain) : Prop := ∀ D R, M.mem D X →
  (∀ x, M.mem x D → ∃ y, M.mem y X ∧ Rd_entry_d x y R) →
    ∃ B, M.mem B X ∧ ∀ x, M.mem x D → ∃ y, M.mem y B ∧ Rd_entry_d x y R

def sc_bound_m {d} (X : Term d) : Formula 1 d := set[d] ⟪
  ∀ D ∈ ⌜X⌝ₛ, ∀ R,
    (∀ x ∈ D, ∃ y ∈ ⌜X⌝ₛ, ⌜rd_entry0_m⌝ₚ(x, y, R)) →
      ∃ B ∈ ⌜X⌝ₛ, ∀ x ∈ D, ∃ y ∈ B, ⌜rd_entry0_m⌝ₚ(x, y, R)⟫
derive_free_closed sc_bound_m

theorem sc_bound_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X : Term d) :
    Formula.satisfies ρ (sc_bound_m X) ↔ Sc_bound_d (X.eval ρ) := by
  simp only [sc_bound_m, Sc_bound_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken]
  exact ⟨fun h D R hd => h D hd R, fun h D hd R => h D R hd⟩

/-- 界来自原不可达层的遗传大小闭包，选择函数在原背景中实际构造。 -/
theorem sc_v_bound_l (hZFC : M.Models ZFC) {ω κ X : M.Domain} (hω : M.IsOmega ω)
    (above : M.mem ω κ) (regular : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (strong : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) κ X) : Sc_bound_d X := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hereditary := ZFC.inaccessible_hereditary_l I hZFC hω above regular strong rank
  intro D R hd total
  let ρ : Env M 1 := ⟨fun _ => R, fun _ => R⟩
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 1) .newest (.bound 2) }
  have read x y : φ.denote ρ x y ↔ Rd_entry_d x y R := rd_entry0_sat_l hZF.1 ..
  obtain ⟨q, fn, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := D) (Y := X)
    (fun x hx => (total x hx).imp (fun y hy => ⟨hy.1, (read x y).mpr hy.2⟩))
  obtain ⟨B, range⟩ := ZF.exists_range_of_setFunction hZF I fn.1 fn.2.1
  have fb : M.IsSetFunctionFromTo I q D B := ⟨fn.1, fn.2.1,
    fun x hx => (fn.2.2 x hx).imp (fun y hy => ⟨(range y).mpr ⟨x, hy.2⟩, hy.2⟩)⟩
  obtain ⟨μ, hm, small⟩ := ZF.hmem_size_l I hZF ((hereditary D).mp hd)
  have size := ZF.ordinal_image_bound_l I hZF (regular.1.1.mem hm) small fb
    (fun y hy => ((range y).mp hy).imp (fun x hx => ⟨fn.input_mem_of_pairMember hx, hx⟩))
  have hb := ZFC.h_small_closed_l I hZFC hω regular above hereditary
    (fun y hy => ((range y).mp hy).elim (fun _ hx => fn.output_mem_of_pairMember hx)) hm size
  exact ⟨B, hb, fun x hx => (fb.2.2 x hx).imp (fun y hy => ⟨hy.1, (read x y).mp (select x y hy.2)⟩)⟩

/-- 关系收集界先回收函数值域，再由同一极限秩历史回收整张图。 -/
theorem Sc_bound_d.function_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    {δ X D f : M.Domain} (bound : Sc_bound_d X) (rank : V_d I δ X)
    (limit : M.IsLimitOrdinal δ) (hD : M.mem D X) (fn : Fn0_d D X f) : Sfun_d X D f := by
  obtain ⟨B, hB, cover⟩ := bound D f hD (fun x hx => fn.2.1 x hx)
  have fb : Fn0_d D B f := fn.retarget_l (fun x y hxy => by
    obtain ⟨z, hz, hxz⟩ := cover x (fn.bound_l hxy).1
    have eq := fn.2.2 x (fn.bound_l hxy).1 y (fn.bound_l hxy).2 z (fn.bound_l hxz).2 hxy hxz
    exact eq.symm ▸ hz)
  obtain ⟨U, hU, du, bu⟩ := v_joint_bound_l I rank hD hB
  refine ⟨v_relation_mem_l I rank limit hU (fun p hp => ?_), B, hB, fb⟩
  obtain ⟨x, hx, y, hy, pair⟩ := fb.1 p hp
  exact ⟨x, du x hx, y, bu y hy, pair⟩

/-- 有界二元公式在给定笛卡尔积中分离成原 Kuratowski 关系。 -/
private theorem sc_bound_graph_l (hKP : M.Models KP) {n} (φ : Delta0BinarySchema n)
    (ρ : Env M n) (X Y : M.Domain) : ∃ R, ∀ x y,
      Rd_entry_d x y R ↔ M.mem x X ∧ M.mem y Y ∧ φ.toBinarySchema.denote ρ x y := by
  obtain ⟨P, product⟩ := KP.kprod_exists_l hKP X Y
  let η := (ρ.push X).push Y
  let ψ : Delta0UnarySchema (n + 2) := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2) (.conj
      (kpair0_m (.bound 2) (.bound 1) .newest)
      (binary_pred_m φ.toBinarySchema (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 1) .newest)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (φ.delta0.bind_l _))) }
  have read p : ψ.toUnarySchema.denote η p ↔ ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧
      KPair_d M p x y ∧ φ.toBinarySchema.denote ρ x y := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hKP.1, binary_pred_sat_l]
    rfl
  obtain ⟨R, spec⟩ := KP.separation_exists_d hKP ψ η P
  refine ⟨R, fun x y => ⟨?_, ?_⟩⟩
  · rintro ⟨p, code, hp⟩
    obtain ⟨a, ha, b, hb, pair, valid⟩ := (read p).mp ((spec p).mp hp).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M code pair
    exact ⟨ha, hb, valid⟩
  · rintro ⟨hx, hy, valid⟩
    obtain ⟨p, code⟩ := (kp_pair_l hKP).total x y
    exact ⟨p, code, (spec p).mpr ⟨(product p).mpr ⟨x, hx, y, hy, code⟩,
      (read p).mpr ⟨x, hx, y, hy, code, valid⟩⟩⟩

/-- 原公式先在载体上有界化；关系收集界给出每个收集模式的实际见证集。 -/
theorem Sc_bound_d.models_l (hKP : M.Models KP) {X : M.Domain} (bound : Sc_bound_d X)
    (trans : M.TransitiveSet X)
    (closed : ∀ D, M.mem D X → ∀ A, M.MemberSubset A D → M.mem A X)
    (nx : Nonempty {x // M.mem x X})
    (base : ∀ ρ : Env (rt_model_l X nx) 0, Formula.satisfies ρ zc_base_m) :
    (rt_model_l X nx).Models ZFC := by
  let N := rt_model_l X nx
  have collect {p} (φ : BinarySchema p) (ρ : Env N p) (D : N.Domain)
      (total : ∀ x, N.mem x D → ∃ y, φ.denote ρ x y) :
      ∃ B : N.Domain, ∀ x, N.mem x D → ∃ y, N.mem y B ∧ φ.denote ρ x y := by
    let η : Env M (p+1) := (image_env_l (M := N) (N := M) Subtype.val ρ).push X
    let ψ : Delta0BinarySchema (p+1) := {
      body := lr_rel_m φ.body (.bound 2)
        (Fin.cases .newest (Fin.cases (.bound 1) (fun i => .bound i.succ.succ.succ)))
      freeClosed := lr_rel_closed_l φ.body φ.freeClosed _ _ rfl
        (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
      delta0 := lr_rel_delta_l .. }
    have read (x y : N.Domain) : ψ.toBinarySchema.denote η x.val y.val ↔ φ.denote ρ x y :=
      sc_relative_sat_l trans nx φ.body φ.freeClosed ((ρ.push x).push y) ((η.push x.val).push y.val)
        (.bound 2) _ rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
    obtain ⟨R, graph⟩ := sc_bound_graph_l hKP ψ η D.val X
    obtain ⟨B, hb, witnesses⟩ := bound D.val R D.property (fun x hx => by
      let a : N.Domain := ⟨x, trans D.val D.property x hx⟩
      obtain ⟨b, valid⟩ := total a hx
      exact ⟨b.val, b.property, (graph x b.val).mpr ⟨hx, b.property, (read a b).mpr valid⟩⟩)
    refine ⟨⟨B, hb⟩, fun x hx => ?_⟩
    obtain ⟨y, hy, pair⟩ := witnesses x.val hx
    let b : N.Domain := ⟨y, trans B hb y hy⟩
    exact ⟨b, hy, (read x b).mp ((graph x.val y).mp pair).2.2⟩
  have separate {p} (φ : UnarySchema p) (ρ : Env N p) (D : N.Domain) :
      ∃ A : N.Domain, ∀ x, N.mem x A ↔ N.mem x D ∧ φ.denote ρ x := by
    let η : Env M (p+1) := (image_env_l (M := N) (N := M) Subtype.val ρ).push X
    let ψ : Delta0UnarySchema (p+1) := {
      body := lr_rel_m φ.body (.bound 1) (Fin.cases .newest (fun i => .bound i.succ.succ))
      freeClosed := lr_rel_closed_l φ.body φ.freeClosed _ _ rfl (Fin.cases rfl (fun _ => rfl))
      delta0 := lr_rel_delta_l .. }
    have read (x : N.Domain) : ψ.toUnarySchema.denote η x.val ↔ φ.denote ρ x :=
      sc_relative_sat_l trans nx φ.body φ.freeClosed (ρ.push x) (η.push x.val)
        (.bound 1) _ rfl (Fin.cases rfl (fun _ => rfl))
    obtain ⟨A, spec⟩ := KP.separation_exists_d hKP ψ η D.val
    have ha := closed D.val D.property A (fun x hx => ((spec x).mp hx).1)
    exact ⟨⟨A, ha⟩, fun x => (spec x.val).trans (and_congr_right fun _ => read x)⟩
  refine ⟨rt_model_ext_l hKP.1 trans nx, fun s hs => ?_⟩
  rw [Structure.satisfiesSentence_iff]
  intro f
  have hb := base ⟨Fin.elim0, f⟩
  simp only [zc_base_m, Formula.satisfies_conj_iff] at hb
  cases hs with
  | choice => exact hb.2.2.2.2.2.2.2
  | zf hs =>
    cases hs with
    | extensionality => exact hb.1
    | emptySet => exact hb.2.1
    | pairing => exact hb.2.2.1
    | union => exact hb.2.2.2.1
    | powerSet => exact hb.2.2.2.2.1
    | infinity => exact hb.2.2.2.2.2.1
    | foundation => exact hb.2.2.2.2.2.2.1
    | separation φ =>
      apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.separationCore φ)).mpr
      intro b
      exact (Axioms.Schema.separation_sat_iff_d ⟨b, f⟩ φ).mpr (separate φ ⟨b, f⟩)
    | collection φ =>
      apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.collectionCore φ)).mpr
      intro b
      exact (Axioms.Schema.collection_sat_iff_d ⟨b, f⟩ φ).mpr (collect φ ⟨b, f⟩)

end YesMetaZFC.SetTheory.Internal

/-! ## 从内部 ZFC 导出原递归所需的源理论

原关系中的 ZFC 证书直接给出完整源理论。普通收集先在同一结构中给出
集合界，全内部分离构造原关系真值图，内部选择再产生实际统一函数。
没有把统一化或小定义域收集写进 ZFC 证书的假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem sc_algebra_models_l (h : M.Models ZFC) (ρ : Env M 0) : Formula.satisfies ρ sc_algebra_m := by
  let hf := ZFC.models_zf_l h
  let hk := ZF.modelsKP hf
  simp only [sc_algebra_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, pair0_sat_l h.1, rd_graph_sat_l hk,
    sc_total0_sat_l h.1, fn0_sat_l h.1, Formula.satisfies_subset_iff]
  refine ⟨⟨KP.exists_pair hk, KP.exists_union hk, ?_, fun _ _ _ ht => sc_choice_graph_l h ht⟩,
    rd_fibers_exists_l hk⟩
  intro A B
  obtain ⟨P, hp⟩ := ZF.exists_cartesianProduct hf (kp_pair_l hk) A B
  exact ⟨P, fun t => (hp t).trans ⟨fun ⟨x, hx, y, hy, pair⟩ => ⟨x, y, hx, hy, pair⟩,
    fun ⟨x, y, hx, hy, pair⟩ => ⟨x, hx, y, hy, pair⟩⟩⟩

section Source
variable (hZF : M.Models ZF) {ω c X R : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Zc_model_d.theory_l (hω : M.IsOmega ω) (h : Zc_model_d I ω c X R) : Sc_theory_d I ω X R :=
  ⟨h.schemas.separation, fun _ ρ => sc_algebra_models_l (h.native_l I hZF hω) ρ⟩

theorem Zc_model_d.power_l (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (h : Zc_model_d I ω c X R) : Sc_power_d X := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  let nx : Nonempty {x // M.mem x X} := ⟨⟨x, hx⟩⟩
  apply (sc_power_sat_l hX nx ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩).mp
  simp only [sc_power_m, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isPowerSet_iff]
  exact ZF.exists_powerSet (ZFC.models_zf_l (h.membership_l I hZF hω hm nx))

theorem Zc_model_d.collection_l (hω : M.IsOmega ω) (h : Zc_model_d I ω c X R) :
    Sc_collection_d I ω X R := by
  let N := smdl_structure_l I (R := R) h.model.2.1
  have native := h.native_l I hZF hω
  let hf := ZFC.models_zf_l native
  let J := kp_pair_l (ZF.modelsKP hf)
  intro _ _ _ _ _ _ E F n r i j f A hE hF hr hi hj hij henv hA _ total
  let A₀ : N.Domain := ⟨A, hA⟩
  obtain ⟨C, hC, bound⟩ := h.schemas.collection E F n r i j f A hE hF hr hi hj hij henv hA total
  let C₀ : N.Domain := ⟨C, hC⟩
  obtain ⟨P, product⟩ := ZF.exists_cartesianProduct hf J A₀ C₀
  obtain ⟨Q, _, graph⟩ := sc_binary_relation_l hZF hω h.model native.1 J h.schemas.separation
    hE hF hr hi hj hij henv A₀ C₀ P product
  obtain ⟨B, fn, sub⟩ := sc_choice_graph_l native (A := A₀) (B := C₀) (R := Q) (fun x hx => by
    obtain ⟨y, hy, hc, ht⟩ := bound x.val x.property hx
    exact ⟨⟨y, hy⟩, hc, (graph x ⟨y, hy⟩).mpr ⟨hx, hc, ht⟩⟩)
  exact ⟨B, C₀, fn, fun x y ⟨p, pair, hp⟩ => ((graph x y).mp ⟨p, pair, sub p hp⟩).2.2⟩

end Source

end YesMetaZFC.SetTheory.Internal

/-! ## 完整内部 ZFC 沿初等图的双向保持

传输模式的内部全称闭包，而非只传输旧参数的实例。目标中的新参数与内部
非标准程序均被覆盖；源和目标都可以是尚未坍塌的关系模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 内部模式量化全部赋值；将全称闭包沿同一初等图双向传输。 -/
theorem Smap_d.schemas_iff_l {ω c d X R Y S q : M.Domain} (hω : M.IsOmega ω)
    (source : Smdl_d I c X R) (model : Smdl_d I d Y S) (map : Smap_d I ω c d X Y q) :
    Zc_schemas_d I ω X R ↔ Zc_schemas_d I ω Y S := by
  have move {c d X R Y S : M.Domain} (source : Smdl_d I c X R) (model : Smdl_d I d Y S)
      (transfer : ∀ n F r E K, Sfm_d I ω n F → M.mem r n →
        M.IsFunctionSpace I E ω X → M.IsFunctionSpace I K ω Y →
        (∀ f, M.mem f E → Ssat_d I X R E F n r f) → ∀ g, M.mem g K → Ssat_d I Y S K F n r g)
      (h : Zc_schemas_d I ω X R) : Zc_schemas_d I ω Y S := by
    constructor
    · intro K F n r i g D hK hF hr hi hg hD
      obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, _, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hi
      obtain ⟨m, G, k, build, code⟩ := sfm_sep_raw_l I hZF hω hF hr hi hs ht hsi hti hst hb htb
      obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
      have valid f (hf : M.mem f E) : Ssat_d I X R E G m k f := by
        obtain ⟨A, hA, ha⟩ := ((hE f).mp hf).2.2 s hs
        exact (code X R E f A hE hf ha).mpr (h.separation E F n r i f A hE hF hr hi hf hA)
      obtain ⟨g', ug, fg⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hD
      obtain ⟨A, hA, sep⟩ := (code Y S K g' D hK ((hK g').mpr fg)
        ((ug.2 s D).mpr (Or.inl ⟨rfl, rfl⟩))).mp
          (transfer _ _ _ _ _ build.program build.root hE hK valid g' ((hK g').mpr fg))
      exact ⟨A, hA, (sr_sep_agree_l I hZF hF hb hr hi hK hg ((hK g').mpr fg) (ug.agree_l I hsb)).mpr sep⟩
    · intro K F n r i j g D hK hF hr hi hj hij hg hD total
      obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, htj, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hj
      obtain ⟨n₁, F₁, r₁, b₁, collect⟩ := sfm_collect_raw_l I hZF hω hF hr hi hj hs ht hsi hti htj hst hb htb
      obtain ⟨n₂, F₂, r₂, b₂, antecedent⟩ := sfm_total_raw_l I hZF hω b₁.program (b₁.span r hr) hi hj hs hsi
      obtain ⟨m, G, k, build, implication⟩ := sfm_imp_l I hZF hω b₂.program b₂.root (b₂.span r₁ b₁.root)
      have initial Z U E f x y : Sbin_d I Z U E F₁ n₁ r i j f x y ↔ Sbin_d I Z U E F n r i j f x y :=
        exists_congr fun v => exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
          (b₁.sat_l I hZF hF hr Z U E w).symm
      have read Z U E a f (md : Smdl_d I a Z U) (A : (smdl_structure_l I (R := U) md.2.1).Domain)
          (hE : M.IsFunctionSpace I E ω Z) (hf : M.mem f E) (ha : M.PairMember I s A.val f) :
          Ssat_d I Z U E G m k f ↔
            ((∀ x : (smdl_structure_l I (R := U) md.2.1).Domain, M.PairMember I x.val A.val U →
              ∃ y : (smdl_structure_l I (R := U) md.2.1).Domain, Sbin_d I Z U E F n r i j f x.val y.val) →
            ∃ C : (smdl_structure_l I (R := U) md.2.1).Domain,
              ∀ x : (smdl_structure_l I (R := U) md.2.1).Domain, M.PairMember I x.val A.val U →
                ∃ y : (smdl_structure_l I (R := U) md.2.1).Domain,
                  M.PairMember I y.val C.val U ∧ Sbin_d I Z U E F n r i j f x.val y.val) := by
        rw [implication Z U E f hf, antecedent Z U E a f md A hE hf ha,
          ← b₂.sat_l I hZF b₁.program b₁.root Z U E f, collect Z U E a f md A hE hf ha]
        exact imp_congr (forall_congr' fun x => imp_congr_right fun _ => exists_congr fun y => initial Z U E f x.val y.val) Iff.rfl
      obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
      have valid f (hf : M.mem f E) : Ssat_d I X R E G m k f := by
        obtain ⟨A, hA, ha⟩ := ((hE f).mp hf).2.2 s hs
        apply (read X R E c f source ⟨A, hA⟩ hE hf ha).mpr
        intro total
        obtain ⟨C, hC, bound⟩ := h.collection E F n r i j f A hE hF hr hi hj hij hf hA
          (fun x hx ha => (total ⟨x, hx⟩ ha).elim fun y hy => ⟨y.val, y.property, hy⟩)
        exact ⟨⟨C, hC⟩, fun x hx => (bound x.val x.property hx).elim fun y ⟨hy, hc, ht⟩ => ⟨⟨y, hy⟩, hc, ht⟩⟩
      obtain ⟨g', ug, fg⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hD
      have hg' := (hK g').mpr fg
      have agree x y (hx : M.mem x Y) (hy : M.mem y Y) :
          Sbin_d I Y S K F n r i j g x y ↔ Sbin_d I Y S K F n r i j g' x y :=
        sbin_agree_l I hZF hF hb hr hi hj hK hg hg' (ug.agree_l I hsb) hx hy
      obtain ⟨C, bound⟩ := (read Y S K d g' model ⟨D, hD⟩ hK hg'
        ((ug.2 s D).mpr (Or.inl ⟨rfl, rfl⟩))).mp
          (transfer _ _ _ _ _ build.program build.root hE hK valid g' hg')
          (fun x hx => (total x.val x.property hx).elim fun y ⟨hy, ht⟩ =>
            ⟨⟨y, hy⟩, (agree x.val y x.property hy).mp ht⟩)
      exact ⟨C.val, C.property, fun x hx hd => (bound ⟨x, hx⟩ hd).elim fun y ⟨hc, ht⟩ =>
        ⟨y.val, y.property, hc, (agree x y.val hx y.property).mpr ht⟩⟩

  exact ⟨move source model (fun _ _ _ _ _ hF hr hE hK => (map.valid_l I hZF hω source model hF hr hE hK).mp),
    move model source (fun _ _ _ _ _ hF hr hE hK => (map.valid_l I hZF hω source model hF hr hK hE).mpr)⟩

theorem Zc_model_d.map_l {ω c d X R Y S q : M.Domain} (hω : M.IsOmega ω)
    (h : Zc_model_d I ω c X R) (model : Smdl_d I d Y S) (map : Smap_d I ω c d X Y q) :
    Zc_model_d I ω d Y S := by
  refine ⟨model, map.extensional_l hZF hω h.model model h.ext, ?_,
    (map.schemas_iff_l hZF hω h.model model).mp h.schemas⟩
  intro η
  obtain ⟨x, hx⟩ := h.model.2.1
  let ρ : Env (smdl_structure_l I (R := R) h.model.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  exact (smap_source_l I hZF hω h.model model map zc_base_m zc_base_closed_l ρ η
    (fun i => Fin.elim0 i)).mp (h.base ρ)

/-- 完整内部 ZFC 沿实际初等图回拉，源不必传递，嵌入不必满射。 -/
theorem Zc_model_d.pull_l {ω c d X R Y S q : M.Domain} (hω : M.IsOmega ω)
    (h : Zc_model_d I ω d Y S) (model : Smdl_d I c X R) (map : Smap_d I ω c d X Y q) :
    Zc_model_d I ω c X R := by
  have ext : Rf_ext_d I X R := by
    obtain ⟨n,F,k,hF,hk,read⟩ := sext_code_l hZF hω
    obtain ⟨E,hE,f,hf⟩ := senv_space_l I hZF ω model.2.1
    obtain ⟨K,hK⟩ := ZF.exists_functionSpace hZF I ω Y
    exact (read X R E f model.2.1 hE hf).mp
      ((map.valid_l I hZF hω model h.model hF hk hE hK).mpr
        (fun g hg => (read Y S K g h.model.2.1 hK hg).mpr h.ext) f hf)
  refine ⟨model,ext,?_,(map.schemas_iff_l hZF hω model h.model).mpr h.schemas⟩
  intro ρ
  obtain ⟨y,hy⟩ := h.model.2.1
  let η : Env (smdl_structure_l I (R := S) h.model.2.1) 0 := ⟨Fin.elim0,fun _ => ⟨y,hy⟩⟩
  exact (smap_source_l I hZF hω model h.model map zc_base_m zc_base_closed_l ρ η
    (fun i => Fin.elim0 i)).mpr (h.base η)

end YesMetaZFC.SetTheory.Internal
