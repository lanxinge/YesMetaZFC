import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptDecode
import YesMetaZFC.SetTheory.LargeCardinal.IterationEmbedding
import YesMetaZFC.SetTheory.Collapse.RelationRank

/-! # 失败的返回嵌入产生联合尝试秩

任何内部下降链都解码为实际共尾枝、传递直接极限及满足根复合式的返回嵌入。
因此反例的尝试关系内部良基，原良基递归给出实际序数值秩函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

include hZF in
theorem It_order_d.omega_root_l {ω T z : M.Domain} (hω : M.IsOmega ω) (h : It_order_d ω T)
    (hz : ∀ x, ¬ M.mem x z) : ∀ k, M.mem k ω → Rd_entry_d z k T := by
  obtain ⟨z', hz', hzω⟩ := hω.1.1
  have eq := hZF.1.eq_of_same_members z' z (fun x => iff_of_false (hz' x) (hz x))
  subst z'
  let φ : UnarySchema 2 := { body := .forallE (.imp
    (.disj (Formula.extensionalEq .newest (.bound 1)) (.mem .newest (.bound 1))) (rd_entry0_m (.bound 2) .newest (.bound 3))) }
  let ρ : Env M 2 := ⟨Fin.cases z (fun _ => T), fun _ => T⟩
  have sat n : φ.denote ρ n ↔ ∀ k, k = n ∨ M.mem k n → Rd_entry_d z k T := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1]; rfl
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · intro a ha
      have eq := hZF.1.eq_of_same_members a z (fun x => iff_of_false (ha x) (hz x))
      subst a
      exact (sat z).mpr (fun k hk => hk.elim (fun e => e ▸ h.refl z hzω) (fun hk => (hz k hk).elim))
    · intro n hn ih m hm
      have hmω : M.mem m ω := by
        obtain ⟨m', hm', hm'ω⟩ := hω.1.2 n hn
        exact Structure.SuccessorOf.eq hZF.1 hm' hm ▸ hm'ω
      have prev k (hk : M.mem k m) : Rd_entry_d z k T :=
        (sat n).mp ih k (((hm k).mp hk).elim Or.inr (fun eq => Or.inl (hZF.1.eq_of_same_members k n eq)))
      refine (sat m).mpr (fun k hk => hk.elim (fun e => ?_) (prev k))
      obtain ⟨p, hp, pred⟩ := h.predecessor n m hmω hm
      exact e ▸ (pred z).mpr (Or.inr (prev p hp))
  exact fun k hk => (sat k).mp (all k hk) k (Or.inl rfl)

theorem ja_counterexample_rank_l {ω T Q G E Y W z π c₀ X₀ V₀ d : M.Domain}
    (hω : M.IsOmega ω) (dc : Dc_d I ω) (h : It_diagram_d hZF ω ω T Q G)
    (en : Ja_enum_d I ω ω Q E) (hz : ∀ x, ¬ M.mem x z)
    (hc : Rd_entry_d z c₀ Q) (mx : Smdl_d I c₀ X₀ V₀) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (pi : Fn0_d X₀ Y π) (bad : ¬ It_return_d hZF ω z T Q G d Y π) :
    ∃ A R β F, Ja_space_d I ω T Q G E Y W z π A R ∧ M.IsOrdinal β ∧
      M.IsSetFunctionFromTo I F A β ∧ Wr_d I A R F := by
  obtain ⟨A, R, space⟩ := ja_space_l hZF hω h en (Y := Y) (W := W) (z := z) (π := π)
  have wf : Wf_rel_d A R := wf_of_no_desc_l hZF dc (fun g fg desc => by
    obtain ⟨B, path⟩ := ja_path_l hZF hω h.order space fg desc
    obtain ⟨P, maps, ps⟩ := ja_decode_l hZF hω h en my.1 space fg path
    have hzω := (h.model_domain z).mpr ⟨c₀, hc⟩
    obtain ⟨k, hk, _⟩ := path.branch.cofinal z hzω
    have hzB := path.branch.down z k (h.order.omega_root_l hZF hω hz k (path.branch.subset k hk)) hk
    have root := ja_root_l hZF en space fg path hzB hc mx pi ps
      (fun f hf => fn0_of_function_l (ZF.modelsKP hZF) (maps.elementary z f c₀ X₀ V₀ hf hc mx).1.1)
      ((maps.domain z).mp hzB)
    exact bad (it_embedding_return_l hZF hω h path.branch hzB hc source my maps root))
  obtain ⟨β, F, hb, hf, _, rank⟩ := wr_exists_l I hZF wf
  exact ⟨A, R, β, F, space, hb, hf, rank⟩

end YesMetaZFC.SetTheory.LargeCardinal
