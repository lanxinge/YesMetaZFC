import YesMetaZFC.SetTheory.Descriptive.TreeCons
import YesMetaZFC.SetTheory.KP.Natural

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

theorem tree_branch_not_wf_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hZF : M.Models ZF) {ω A J T R f : M.Domain} (hω : M.IsOmega ω)
    (hJ : Fseq_space_d I ω A J) (hf : M.IsSetFunctionFromTo I f ω A)
    (hb : Branch_d J T f) (hr : Edge_d I ω T R) : ¬ Wf_rel_d T R := by
  intro hw
  let φ : Delta0UnarySchema 1 := { body := Formula.subset .newest (.bound 1), delta0 := .atom _ _ _ }
  obtain ⟨Q, spec⟩ := KP.separation_exists_d (ZF.modelsKP hZF) φ ⟨fun _ => f, fun _ => f⟩ J
  have read s : M.mem s Q ↔ M.mem s J ∧ M.MemberSubset s f :=
    (spec s).trans (and_congr_right fun _ => Formula.satisfies_subset_iff ..)
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨s, hs, minimal⟩ := hw Q (fun s hs => hb s ((read s).mp hs).1 ((read s).mp hs).2)
    ⟨z, (read z).mpr ⟨(hJ z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩, fun p hp => (hz p hp).elim⟩⟩
  obtain ⟨hsJ, hsf⟩ := (read s).mp hs
  obtain ⟨n, hn, hsn⟩ := (hJ s).mp hsJ
  obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
  obtain ⟨t, htm, htr, _⟩ := ds_prefix_l I hZF hω hf hmω
  have htJ := (hJ t).mpr ⟨m, hmω, htm⟩
  have htf := (ds_restrict_iff_l I htm hf.1).mp htr
  have hst := ds_prefix_mono_l I hsn htm.1 ((ds_restrict_iff_l I hsn hf.1).mpr hsf) htr
    (fun i hi => (hm i).mpr (Or.inl hi))
  exact minimal t ((read t).mpr ⟨htJ, htf⟩) ((hr.2 s t).mpr
    ⟨hb s hsJ hsf, hb t htJ htf, (tree_step_iff_l I hZF hω hn hmω hsn htm).mpr ⟨hm, hst⟩⟩)

end YesMetaZFC.SetTheory.Descriptive
