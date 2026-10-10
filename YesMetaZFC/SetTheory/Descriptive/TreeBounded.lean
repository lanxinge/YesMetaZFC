import YesMetaZFC.SetTheory.Descriptive.TreeCons
import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.SetTheory.Collapse.RelationSequence

/-! # 任意字母表前缀树的有界子边

长度、字母和函数图均限制在实际集合内；子边因而是 Δ₀，可在传递源中分离。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tb_step_d (ω A s t : M.Domain) : Prop := ∃ n, M.mem n ω ∧ ∃ m, M.mem m ω ∧
  Fn0_d n A s ∧ Fn0_d m A t ∧ M.SuccessorOf m n ∧ M.MemberSubset s t

def tb_step_m {n} (ω A s t : Term n) : Formula 1 n := Formula.existsMem ω
  (Formula.existsMem ω.weaken (.conj (fn0_m (.bound 1) A.weaken.weaken s.weaken.weaken)
    (.conj (fn0_m .newest A.weaken.weaken t.weaken.weaken)
      (.conj (KP.succ0_m .newest (.bound 1)) (Formula.subset s.weaken.weaken t.weaken.weaken)))))
derive_free_closed tb_step_m

theorem tb_step_delta_l {n} (ω A s t : Term n) : (tb_step_m ω A s t).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (fn0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (KP.succ0_delta_l ..) (.atom _ _ _)))))

theorem tb_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω A s t : Term n) :
    Formula.satisfies ρ (tb_step_m ω A s t) ↔ Tb_step_d (ω.eval ρ) (A.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [tb_step_m, Tb_step_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, KP.succ0_sat_l hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

theorem tb_step_l (hZF : M.Models ZF) {ω A J s t : M.Domain} (hω : M.IsOmega ω)
    (hJ : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A J) (hs : M.mem s J) (ht : M.mem t J) :
    Tb_step_d ω A s t ↔ Step_d (kp_pair_l (ZF.modelsKP hZF)) ω s t := by
  obtain ⟨n, hn, hsn⟩ := (hJ s).mp hs
  obtain ⟨m, hm, htm⟩ := (hJ t).mp ht
  refine ⟨fun ⟨l, hl, k, hk, hf, hg, h⟩ =>
    (tree_step_iff_l _ hZF hω hl hk (fn0_function_l (ZF.modelsKP hZF) hf) (fn0_function_l (ZF.modelsKP hZF) hg)).mpr h,
    fun h => ⟨n, hn, m, hm, fn0_of_function_l (ZF.modelsKP hZF) hsn, fn0_of_function_l (ZF.modelsKP hZF) htm,
      (tree_step_iff_l _ hZF hω hn hm hsn htm).mp h⟩⟩

/-- 实际无限枝的全部有限前缀组成真实 ω 下降链。 -/
theorem tree_branch_desc_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF) {ω A J T R f : M.Domain} (hω : M.IsOmega ω)
    (hJ : Fseq_space_d I ω A J)
    (hf : M.IsSetFunctionFromTo I f ω A)
    (hb : Branch_d J T f) (hr : Edge_d I ω T R) :
    ∃ G, Fn0_d ω T G ∧ Wf_desc_d R G := by
  let φ : BinarySchema 1 := { body := Formula.isRestriction 𝒞 .newest (.bound 2) (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
  have sat n s : φ.denote ρ n s ↔ M.IsRestrictionOf I s f n := Formula.satisfies_isRestriction_iff I ..
  obtain ⟨G, fn, select⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ (source := ω) (target := T)
    (fun n hn => (ds_prefix_l I hZF hω hf hn).imp fun s hs => (sat n s).mpr hs.2.1)
    (fun _ _ _ _ hs ht => ((sat ..).mp hs).eq hZF.1 ((sat ..).mp ht))
    (fun n s hn hs => by
      have res := (sat n s).mp hs
      have fn := res.isSetFunctionFromTo hf (hω.transitive hZF n hn)
      exact hb s ((hJ s).mpr ⟨n, hn, fn⟩) ((ds_restrict_iff_l I fn hf.1).mp res))
  refine ⟨G, fn0_of_function_l (ZF.modelsKP hZF) fn, fun i j s t hs hi hj => ?_⟩
  have si := (sat i s).mp ((select i s).mp hi).2
  have tj := (sat j t).mp ((select j t).mp hj).2
  have hiω := fn.input_mem_of_pairMember hi
  have hjω := fn.input_mem_of_pairMember hj
  have sfn := si.isSetFunctionFromTo hf (hω.transitive hZF i hiω)
  have tfn := tj.isSetFunctionFromTo hf (hω.transitive hZF j hjω)
  exact (hr.2 s t).mpr ⟨fn.output_mem_of_pairMember hi, fn.output_mem_of_pairMember hj,
    (tree_step_iff_l I hZF hω hiω hjω sfn tfn).mpr
      ⟨hs, ds_prefix_mono_l I sfn tfn.1 si tj (fun n hn => (hs n).mpr (Or.inl hn))⟩⟩

end YesMetaZFC.SetTheory.Descriptive
