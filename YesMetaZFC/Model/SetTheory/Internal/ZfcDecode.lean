import YesMetaZFC.Model.SetTheory.Internal.ZfcCode
import YesMetaZFC.Model.SetTheory.Internal.Compiler
import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure
import YesMetaZFC.SetTheory.Collection

/-! # 内部 ZFC 证书的原语言解码

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
