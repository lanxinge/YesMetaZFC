import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Definability

/-! # 规范码名合法性、解码及求值的 Σ₁ 接口 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def pn_decode_s : S1_binary 0 where
  -- V 是语法证书，W 是 rud 闭包证书；其余变量都是它们在共同集合界内的数据。
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
        .conj (rd_triple0_m (.bound 8) (.bound 5) (.bound 4) (.bound 7)) <|
          .conj (KP.ord0_m (.bound 5)) <| .conj (KP.n0_m (.bound 4)) <|
            .conj (.disj (.mem (.bound 3) (.bound 4)) (Formula.extensionalEq (.bound 3) (.bound 4))) <|
              .conj (ps_rank_s.matrix_m Fin.elim0 (.bound 3) (.bound 7) .newest) <|
                .conj (rd_closure_s.matrix_m Fin.elim0 (.bound 5) (.bound 2) (.bound 1)) (.mem (.bound 7) (.bound 2))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (rd_triple0_delta_l ..) (.conj (KP.ord0_delta_l _) (.conj (KP.n0_delta_l _)
        (.conj (.disj (.mem _ _) (.atom _ _ _)) (.conj (ps_rank_s.matrix.delta0.bind_l _)
          (.conj (rd_closure_s.matrix.delta0.bind_l _) (.mem _ _)))))))))))) }

theorem pn_decode_sat_l (hKP : M.Models KP) (ρ : Env M 0) (v c : M.Domain) :
    pn_decode_s.schema.denote ρ v c ↔ ∃ a h, Pn_name_d v a h c := by
  rw [S1_binary.sat_l]
  simp only [pn_decode_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_triple0_sat_l hKP.1,
    KP.ord0_sat_l hKP, KP.n0_sat_l hKP.1, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, po_matrix_env_l ps_rank_s ρ, po_matrix_env_l rd_closure_s ρ]
  change (∃ T a, M.mem a T ∧ ∃ h, M.mem h T ∧ ∃ n, M.mem n T ∧ ∃ C, M.mem C T ∧ ∃ W, M.mem W T ∧
    ∃ V, M.mem V T ∧ Rd_triple_d v a h c ∧ M.IsOrdinal a ∧ KP.N0_d h ∧ (M.mem n h ∨ n = h) ∧
      ps_rank_s.matrix_binary.toBinarySchema.denote (ρ.push n) c V ∧
        rd_closure_s.matrix_binary.toBinarySchema.denote (ρ.push a) C W ∧ M.mem c C) ↔ _
  constructor
  · rintro ⟨T, a, _, h, _, n, _, C, _, W, _, V, _, hv, ha, hh, hn, hs, hC, hc⟩
    exact ⟨a, h, hv, ha, hh, ⟨n, hn, (ps_rank_sat_l hKP ρ n c).mp ((ps_rank_s.sat_l ρ n c).mpr ⟨V, hs⟩)⟩,
      C, (rd_closure_sat_l hKP.1 ρ a C).mp ((rd_closure_s.sat_l ρ a C).mpr ⟨W, hC⟩), hc⟩
  · rintro ⟨a, h, hv, ha, hh, ⟨n, hn, hs⟩, C, hC, hc⟩
    obtain ⟨V, hs⟩ := (ps_rank_s.sat_l ρ n c).mp ((ps_rank_sat_l hKP ρ n c).mpr hs)
    obtain ⟨W, hC⟩ := (rd_closure_s.sat_l ρ a C).mp ((rd_closure_sat_l hKP.1 ρ a C).mpr hC)
    obtain ⟨T, ht⟩ := cp_cover_l hKP [a, h, n, C, W, V]
    exact ⟨T, a, (ht a (by simp)).2, h, (ht h (by simp)).2, n, (ht n (by simp)).2,
      C, (ht C (by simp)).2, W, (ht W (by simp)).2, V, (ht V (by simp)).2, hv, ha, hh, hn, hs, hC, hc⟩

def pn_valid_m {n} (v : Term n) : Formula 1 n := .existsE (binary_pred_m pn_decode_s.schema Fin.elim0 v.weaken .newest)
derive_free_closed pn_valid_m
theorem pn_valid_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (v : Term n) :
    Formula.satisfies ρ (pn_valid_m v) ↔ Pn_valid_d (v.eval ρ) := by
  simp only [pn_valid_m, Formula.satisfies_exists_iff, binary_pred_sat_l, pn_decode_sat_l hKP,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken, Pn_valid_d]
  exact ⟨fun ⟨c, a, h, hn⟩ => ⟨a, h, c, hn⟩, fun ⟨a, h, c, hn⟩ => ⟨c, a, h, hn⟩⟩

def pn_eval_s : S1_binary 0 := pn_decode_s.comp pc_eval_s
theorem pn_eval_sat_l (hKP : M.Models KP) (ρ : Env M 0) (v x : M.Domain) :
    pn_eval_s.schema.denote ρ v x ↔ Pn_eval_d v x := by
  rw [pn_eval_s, S1_binary.comp_sat_l hKP]
  simp only [pn_decode_sat_l hKP, pc_eval_sat_l hKP, Pn_eval_d]
  exact ⟨fun ⟨c, ⟨a, h, hv⟩, hx⟩ => ⟨a, h, c, hv, hx⟩, fun ⟨a, h, c, hv, hx⟩ => ⟨c, ⟨a, h, hv⟩, hx⟩⟩

/-- 给定一个合法名字，其所有合法前驱都有统一的模型内集合界。 -/
theorem pn_initial_bound_l (hM : M.Models KPi) {w : M.Domain} (hw : Pn_valid_d w) :
    ∃ B, ∀ v, Pn_valid_d v → Pn_lt_d v w → M.mem v B := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨a, h, c, hw, ha, hh, hc, C, hC, hcC⟩ := hw
  obtain ⟨S, hs⟩ := KP.exists_successor hKP a
  obtain ⟨ω, hω⟩ := omega0_exists_l hM
  obtain ⟨B, hB⟩ := rd_triples_exists_l hKP S ω C
  refine ⟨B, fun v ⟨b, n, d, hv, _, hn, _, D, hD, hdD⟩ hlt => ?_⟩
  have hb : M.mem b a ∨ b = a := ((pn_lt_iff_l hv hw).mp hlt).elim Or.inl (fun h => Or.inr h.1)
  have sub : M.MemberSubset b a := fun x hx => hb.elim (fun hb => ha.transitive b hb x hx) (fun hb => hb ▸ hx)
  have hbS : M.mem b S := (hs b).mpr (hb.imp_right (fun (he : b = a) => he ▸ (fun _ => Iff.rfl)))
  exact (hB v).mpr ⟨b, hbS, n, KPi.n0_in_inductive_l hM hω.1 hn, d, rd_closure_mono_l hM sub hD hC d hdD, hv⟩

end YesMetaZFC.SetTheory.InnerModel
