import YesMetaZFC.SetTheory.Descriptive.GameControl
import YesMetaZFC.SetTheory.Descriptive.TreeDependentChoice
import YesMetaZFC.SetTheory.Collapse.RelationRank
import YesMetaZFC.SetTheory.Descriptive.TreeRankPrefix

/-! # II 获胜策略的合法尝试树有实际序数秩

控制树的一条无限枝同时是合法对局和服从原 II 策略的对局，矛盾。
ZF＋DC 将这一无枝性转为内部良基性，再由原良基递归构造秩函数。
最终证书只检查实际函数图与有界子边，可在后继传递模型中读取。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Cg_control_d.tree_l {ω e X F L G J σ R : M.Domain} (hω : M.IsOmega ω)
    (control : Cg_control_d I ω e X F L G J σ R) : Tree_d F R := by
  refine ⟨fun s hs => ((control.legal s).mp ((control.positions s).mp hs).1).1, ?_⟩
  intro s hs t ht sub
  obtain ⟨legal, follows⟩ := (control.positions s).mp hs
  obtain ⟨n, hn, ft⟩ := (control.space t).mp ht
  obtain ⟨_, _, fs⟩ := (control.space s).mp ((control.legal s).mp legal).1
  have res := (ds_restrict_iff_l I ft fs.1).mpr sub
  refine (control.positions t).mpr ⟨control.legal.prefix_l legal ht sub, ?_⟩
  intro i hi turn h rh v hv
  have hin := ft.input_mem_of_pairMember hv
  have rs : M.IsRestrictionOf I h s i := ⟨rh.1, fun k a => (rh.2 k a).trans
    ⟨fun ⟨hk, ht⟩ => ⟨hk, (res.2 k a).mp ht |>.2⟩,
      fun ⟨hk, hs⟩ => ⟨hk, (res.2 k a).mpr ⟨(hω.members_areOrdinals hZF n hn).transitive i hin k hk, hs⟩⟩⟩⟩
  exact follows i hi turn h rs v
    (hv.elim fun p hp => ⟨p, hp.1, sub p hp.2⟩)

theorem Cg_control_d.no_branch_l {ω e X F L G J B W σ R f : M.Domain} (hω : M.IsOmega ω)
    (control : Cg_control_d I ω e X F L G J σ R) (runs : M.IsFunctionSpace I B ω X)
    (payoff : Cg_payoff_d (M := M) ω X F L J B W) (win : Cg_win_d I false ω X F J B W σ)
    (ff : M.IsSetFunctionFromTo I f ω X) : ¬ Branch_d F R f := by
  intro branch
  have hf := (runs f).mpr ff
  have legal := payoff.all_legal_l hf (fun s hs sf =>
    control.legal.current_l ((control.positions s).mp (branch s hs sf)).1)
  apply win.2 f hf ?_ legal
  intro i hi turn h rh v hv
  obtain ⟨j, succ, hj⟩ := hω.1.2 i hi
  obtain ⟨t, ft, rt, _⟩ := ds_prefix_l I hZF hω ff hj
  have tf := (ds_restrict_iff_l I ft ff.1).mp rt
  have ht := branch t ((control.space t).mpr ⟨j, hj, ft⟩) tf
  have fh := rh.isSetFunctionFromTo ff (hω.transitive hZF i hi)
  have ht' := ds_prefix_mono_l I fh ft.1 rh rt (fun x hx => (succ x).mpr (Or.inl hx))
  exact ((control.positions t).mp ht).2 i hi turn h ((ds_restrict_iff_l I fh ft.1).mpr ht')
    v ((rt.2 i v).mpr ⟨succ.predecessor_mem, hv⟩)

structure Cg_rank_d (ω X R α F : M.Domain) : Prop where
  ordinal : M.IsOrdinal α
  function : Fn0_d R α F
  decrease : ∀ s t a b, Rd_entry_d s a F → Rd_entry_d t b F → Tb_step_d ω X s t → M.mem b a
  proper : ∀ s t a b, Rd_entry_d s a F → Rd_entry_d t b F → M.MemberSubset s t → s ≠ t → M.mem b a

def cg_rank0_m {d} (ω X R α F : Term d) : Formula 1 d := set[d] ⟪
  ⌜KP.ord0_m⌝ₚ(⌜α⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜R⌝ₛ, ⌜α⌝ₛ, ⌜F⌝ₛ) ∧
  (∀ s ∈ ⌜R⌝ₛ, ∀ t ∈ ⌜R⌝ₛ, ∀ a ∈ ⌜α⌝ₛ, ∀ b ∈ ⌜α⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(s, a, ⌜F⌝ₛ) → ⌜rd_entry0_m⌝ₚ(t, b, ⌜F⌝ₛ) →
    ⌜tb_step_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, s, t) → b ∈ a) ∧
  (∀ s ∈ ⌜R⌝ₛ, ∀ t ∈ ⌜R⌝ₛ, ∀ a ∈ ⌜α⌝ₛ, ∀ b ∈ ⌜α⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(s, a, ⌜F⌝ₛ) → ⌜rd_entry0_m⌝ₚ(t, b, ⌜F⌝ₛ) → s ⊆ t → ¬ (s = t) → b ∈ a)⟫
derive_free_closed cg_rank0_m

theorem cg_rank0_delta_l {d} (ω X R α F : Term d) : (cg_rank0_m ω X R α F).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (fn0_delta_l ..) (.conj
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.imp (tb_step_delta_l ..) (.mem ..))))))))
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
      (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.imp (.atom ..) (.imp (.neg (.atom ..)) (.mem ..)))))))))))

theorem cg_rank0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω X R α F : Term d) :
    Formula.satisfies ρ (cg_rank0_m ω X R α F) ↔
      Cg_rank_d (ω.eval ρ) (X.eval ρ) (R.eval ρ) (α.eval ρ) (F.eval ρ) := by
  simp only [cg_rank0_m, Formula.satisfies_conj_iff, KP.ord0_sat_l hKP, fn0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1,
    tb_step_sat_l hKP.1, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨ha, fn, decrease, proper⟩ => ⟨ha, fn, fun s t a b hs ht step => decrease s (fn.bound_l hs).1
      t (fn.bound_l ht).1 a (fn.bound_l hs).2 b (fn.bound_l ht).2 hs ht step,
      fun s t a b hs ht => proper s (fn.bound_l hs).1 t (fn.bound_l ht).1 a (fn.bound_l hs).2 b (fn.bound_l ht).2 hs ht⟩,
    fun rank => ⟨rank.ordinal, rank.function, fun s _ t _ a _ b _ => rank.decrease s t a b,
      fun s _ t _ a _ b _ => rank.proper s t a b⟩⟩

def cg_rank_m {d} (ω X R : Term d) : Formula 1 d := .existsE (.existsE
  (cg_rank0_m ω.weaken.weaken X.weaken.weaken R.weaken.weaken (.bound 1) .newest))
derive_free_closed cg_rank_m

theorem Cg_control_d.rank_l {ω e X F L G J B W σ R : M.Domain} (hω : M.IsOmega ω) (dc : Dc_d I ω)
    (control : Cg_control_d I ω e X F L G J σ R) (runs : M.IsFunctionSpace I B ω X)
    (payoff : Cg_payoff_d (M := M) ω X F L J B W) (win : Cg_win_d I false ω X F J B W σ) :
    ∃ α H, Cg_rank_d ω X R α H := by
  obtain ⟨E, edges⟩ := tree_edges_l I hZF ω R
  have wf := tree_wf_dc_l I hZF hω dc control.space (control.tree_l hZF hω) edges
    (fun _ ff => control.no_branch_l hZF hω runs payoff win ff)
  obtain ⟨α, H, ha, fn, _, rank⟩ := wr_exists_l I hZF wf
  have decrease s t a b (hs : Rd_entry_d s a H) (ht : Rd_entry_d t b H) (step : Tb_step_d ω X s t) : M.mem b a := by
    have hsR := fn.input_mem_of_pairMember hs
    have htR := fn.input_mem_of_pairMember ht
    exact ((rank.2.2 s a hs).2 b).mpr ⟨t, b, htR, (edges.2 s t).mpr
      ⟨hsR, htR, (tb_step_l hZF hω control.space ((control.tree_l hZF hω).1 s hsR)
        ((control.tree_l hZF hω).1 t htR)).mp step⟩, ht, Or.inl rfl⟩
  exact ⟨α, H, ha, fn0_of_function_l (ZF.modelsKP hZF) fn, decrease,
    tb_rank_prefix_l hZF hω control.space (control.tree_l hZF hω) ha (fn0_of_function_l (ZF.modelsKP hZF) fn) decrease⟩

include hZF in
/-- 实际秩函数排除任意内部无限逐项延长链；这里不再使用 DC。 -/
theorem Cg_rank_d.no_chain_l {ω X R α F H : M.Domain} (hω : M.IsOmega ω)
    (rank : Cg_rank_d ω X R α F) (fn : Fn0_d ω R H) :
    ¬ (∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H → Tb_step_d ω X s t) := by
  intro next
  obtain ⟨G, gf, read⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) fn) (fn0_function_l (ZF.modelsKP hZF) rank.function)
  obtain ⟨E, wf, edges⟩ := wf_membership_l hZF α
  apply wf_no_desc_l hZF hω wf (fn0_of_function_l (ZF.modelsKP hZF) gf)
  intro i j a b succ ha hb
  obtain ⟨_, s, hs, sa⟩ := (read i a).mp ha
  obtain ⟨_, t, ht, tb⟩ := (read j b).mp hb
  exact (edges b a).mpr ⟨gf.output_mem_of_pairMember hb, gf.output_mem_of_pairMember ha,
    rank.decrease s t a b sa tb (next i j s t succ hs ht)⟩

end YesMetaZFC.SetTheory.Descriptive
