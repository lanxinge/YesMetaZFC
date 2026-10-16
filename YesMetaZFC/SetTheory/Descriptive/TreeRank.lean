import YesMetaZFC.SetTheory.Descriptive.TreeDependentChoice
import YesMetaZFC.SetTheory.Collapse.RelationRank
import YesMetaZFC.SetTheory.Descriptive.TreeRankPrefix

/-! # 任意集合树的序数秩证书

DC 只用于从无枝性推出良基性。产生实际有界秩之后，排除新分支只需 ZF。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

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

theorem tree_rank_l {ω X F T : M.Domain} (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T)
    (no : ∀ f, M.IsSetFunctionFromTo I f ω X → ¬ Branch_d F T f) :
    ∃ α H, Cg_rank_d ω X T α H := by
  obtain ⟨E, edges⟩ := tree_edges_l I hZF ω T
  obtain ⟨α, H, ha, fn, _, rank⟩ := wr_exists_l I hZF
    (tree_wf_dc_l I hZF hw dc space tree edges no)
  have decrease s t a b (hs : Rd_entry_d s a H) (ht : Rd_entry_d t b H)
      (step : Tb_step_d ω X s t) : M.mem b a := by
    have hsT := fn.input_mem_of_pairMember hs
    have htT := fn.input_mem_of_pairMember ht
    exact ((rank.2.2 s a hs).2 b).mpr ⟨t, b, htT, (edges.2 s t).mpr
      ⟨hsT, htT, (tb_step_l hZF hw space (tree.1 s hsT) (tree.1 t htT)).mp step⟩, ht, Or.inl rfl⟩
  exact ⟨α, H, ha, fn0_of_function_l (ZF.modelsKP hZF) fn, decrease,
    tb_rank_prefix_l hZF hw space tree ha (fn0_of_function_l (ZF.modelsKP hZF) fn) decrease⟩

theorem Cg_rank_d.no_branch_l {ω X F T α H f : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F T) (rank : Cg_rank_d ω X T α H)
    (ff : M.IsSetFunctionFromTo I f ω X) : ¬ Branch_d F T f := by
  intro branch
  obtain ⟨E, edges⟩ := tree_edges_l I hZF ω T
  obtain ⟨G, fn, chain⟩ := tree_branch_desc_l I hZF hw space ff branch edges
  apply rank.no_chain_l hZF hw fn
  intro i j s t succ hs ht
  exact (tb_step_l hZF hw space (tree.1 s (fn.bound_l hs).2)
    (tree.1 t (fn.bound_l ht).2)).mpr (((edges.2 s t).mp (chain i j s t succ hs ht)).2.2)

end YesMetaZFC.SetTheory.Descriptive
