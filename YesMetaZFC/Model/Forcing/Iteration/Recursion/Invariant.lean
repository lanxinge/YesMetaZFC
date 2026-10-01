import YesMetaZFC.Model.Forcing.Iteration.Recursion.Step
import YesMetaZFC.Model.Forcing.Iteration.Recursion.InvariantSyntax

/-! # 任意内部长度递归轨迹的阶段系统不变式

对实际公式“每张该长度递归图均为合法历史”作内部序数归纳。所有旧阶段来自
更短的递归前缀，投影与限制交换保证新链接连接的是原来的同一阶段。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_recursive_good_l (hZF : M.Models ZF) {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {k ω e α S}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (hRule : Row_rule_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω φ ρ)
    (hRec : M.IsRecursiveSequence (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)))
      (Row_op_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e φ ρ) S α) :
    ∃ F H, Row_good_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω e S α F H := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ψ := row_invariant_s φ k
  let η := row_op_env_l ρ ω e
  apply (row_invariant_sat_l I hZF.1 φ ρ k ω e α).mp ?_ S hRec
  apply hRec.1.1.induction (fun β => ψ.denote η β)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF ψ.neg η α
    refine ⟨C, fun β => ?_⟩
    simpa only [UnarySchema.denote, UnarySchema.neg, Formula.satisfies_neg_iff] using hC β
  · intro β hβ ih
    apply (row_invariant_sat_l I hZF.1 φ ρ k ω e β).mpr
    intro T hT
    -- 每个实际输出来自较短的合法历史，故确为一个新的偏序对。
    have step i c (hic : Entry_d M i c T) :
        ∃ Q F H D V, M.IsRestrictionOf I Q T i ∧ Row_good_d I k ω e Q i F H ∧
          KPair_d M c D V ∧ Row_extend_d I k ω i F H e D V := by
      have hi := (hT.1.2.2 i).mpr ⟨c, hic⟩
      obtain ⟨Q, hQ, hc⟩ := hT.2 i hi c hic
      obtain ⟨F, H, hg⟩ := (row_invariant_sat_l I hZF.1 φ ρ k ω e i).mp (ih i hi) Q (hT.restriction hi hQ)
      obtain ⟨D, V, hdv, _, hExt⟩ := row_op_extend_l hZF hω hRule hg hc
      exact ⟨Q, F, H, D, V, hQ, hg, hdv, hExt⟩
    have hpairs i c (hic : Entry_d M i c T) : ∃ D V, KPair_d M c D V := by
      obtain ⟨_, _, _, D, V, _, _, hc, _⟩ := step i c hic
      exact ⟨D, V, hc⟩
    obtain ⟨F, H, hh, hF, hH⟩ := row_history_exists_l hZF hT.1 hpairs
    -- 双投影在每个前缀上与归纳所得系统相同，故可直接转移前缀链接。
    have stage i B R (hB : Entry_d M i B F) (hR : Entry_d M i R H) :
        Row_stage_d M i B R e ∧ (∀ p, M.mem p B → Row_supp_d I k ω p) ∧
        ∀ j P V, M.mem j i → Entry_d M j P F → Entry_d M j V H → Row_link_d I j P V B R := by
      obtain ⟨c, hic, hbr⟩ := (row_history_entry_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hT.1 hh i B R).mp ⟨hB, hR⟩
      obtain ⟨Q, A, C, D, V, hQ, hg, hdv, hExt⟩ := step i c hic
      obtain ⟨hb, hr⟩ := kpair_injective_l M hbr hdv
      subst D; subst V
      have hA := row_part_restrict_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hQ hh.1 hg.2.1.1
      have hC := row_part_restrict_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hQ hh.2 hg.2.1.2
      exact ⟨hExt.1, hExt.2.2, fun j P V hji hp hv =>
        hExt.2.1 j P V ((hA.2 j P).mpr ⟨hji, hp⟩) ((hC.2 j V).mpr ⟨hji, hv⟩)⟩
    refine ⟨F, H, hT.1, hh, ⟨hF, hH, he, fun i B R hB hR => (stage i B R hB hR).1, ?_⟩, ?_⟩
    · intro i j B R D V hB hR hD hV hij
      have hi := (hF.2.2 i).mpr ⟨B, hB⟩
      have hj := (hF.2.2 j).mpr ⟨D, hD⟩
      rcases hβ.wellOrder.linear.compare i hi j hj with hEq | hij' | hji
      · have heq := hZF.1.eq_of_same_members i j hEq
        subst j
        have hb := hF.2.1.2 i B D hB hD
        have hv := hH.2.1.2 i R V hR hV
        subst D; subst V
        exact row_link_id_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) (stage i B R hB hR).1.order (stage i B R hB hR).1.rows
      · exact (stage j D V hD hV).2.2 i B R hij' hB hR
      · exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) j (hij j hji))
    · intro i B hB p hp
      obtain ⟨R, hR⟩ := (hH.2.2 i).mp ((hF.2.2 i).mpr ⟨B, hB⟩)
      exact (stage i B R hB hR).2.1 p hp

end YesMetaZFC.Model.Forcing.Internal
