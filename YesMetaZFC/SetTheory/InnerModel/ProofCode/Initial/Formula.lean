import YesMetaZFC.SetTheory.InnerModel.ProofCode.Initial.Bounding

/-! # 精确全局初段的 Σ₁ 构造证书

先构造 (α+1)×ω×rud(α)，用总语法检查器分离全部合法码名，最后按规范码序
取目标之前的切片。证书只保存这些实际计算的中间集合及其有界验证材料。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pi_build_d (w I : M.Domain) : Prop := ∃ a h c ω C B D,
  Rd_triple_d w a h c ∧ M.IsOrdinal a ∧ Omega0_d ω ∧ Rd_closure_d a C ∧ Pi_box_d a ω C B ∧
    pg_filter_s.schema.denote (rd_seed_env_l C) B D ∧ M.mem w D ∧ pi_slice_s.schema.denote (rd_seed_env_l w) D I

def pi_initial_s : S1_binary 0 where
  matrix := {
    -- 量词之后为 Wi,Wd,Wr,D,B,P,S,C,ω,c,h,α,T,I,w。
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <| Formula.existsMem (.bound 5) <|
      Formula.existsMem (.bound 6) <| Formula.existsMem (.bound 7) <| Formula.existsMem (.bound 8) <|
      Formula.existsMem (.bound 9) <| Formula.existsMem (.bound 10) <| Formula.existsMem (.bound 11) <|
        .conj (rd_triple0_m (.bound 14) (.bound 11) (.bound 10) (.bound 9)) <|
          .conj (KP.ord0_m (.bound 11)) <| .conj (omega0_m (.bound 8)) <|
            .conj (KP.succ0_m (.bound 6) (.bound 11)) <|
              .conj (rd_graph_m .prod (.bound 8) (.bound 7) (.bound 8) (.bound 5)) <|
                .conj (rd_graph_m .prod (.bound 6) (.bound 5) (.bound 6) (.bound 4)) <|
                  .conj (rd_closure_s.matrix_m Fin.elim0 (.bound 11) (.bound 7) (.bound 2)) <|
                    .conj (pi_wit_m pg_filter_s (.bound 7) (.bound 4) (.bound 3) (.bound 1)) <|
                      .conj (.mem (.bound 14) (.bound 3)) (pi_wit_m pi_slice_s (.bound 14) (.bound 3) (.bound 13) .newest)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
        (.conj (rd_triple0_delta_l ..) (.conj (KP.ord0_delta_l _) (.conj (omega0_delta_l _)
          (.conj (KP.succ0_delta_l ..) (.conj (rd_graph_delta_l ..) (.conj (rd_graph_delta_l ..)
            (.conj (rd_closure_s.matrix.delta0.bind_l _) (.conj (pg_filter_s.matrix.delta0.bind_l _)
              (.conj (.mem _ _) (pi_slice_s.matrix.delta0.bind_l _))))))))))))))))))))) }

theorem pi_initial_build_l (hKP : M.Models KP) (ρ : Env M 0) (w I : M.Domain) :
    pi_initial_s.schema.denote ρ w I ↔ Pi_build_d w I := by
  rw [S1_binary.sat_l]
  simp only [pi_initial_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hKP.1, KP.ord0_sat_l hKP, omega0_sat_l hKP.1, KP.succ0_sat_l hKP.1, rd_graph_sat_l hKP,
    po_matrix_env_l rd_closure_s ρ, pi_wit_sat_l, Formula.satisfies_mem_iff]
  change (∃ T a, M.mem a T ∧ ∃ h, M.mem h T ∧ ∃ c, M.mem c T ∧ ∃ ω, M.mem ω T ∧ ∃ C, M.mem C T ∧
    ∃ S, M.mem S T ∧ ∃ P, M.mem P T ∧ ∃ B, M.mem B T ∧ ∃ D, M.mem D T ∧ ∃ Wr, M.mem Wr T ∧
    ∃ Wd, M.mem Wd T ∧ ∃ Wi, M.mem Wi T ∧ Rd_triple_d w a h c ∧ M.IsOrdinal a ∧ Omega0_d ω ∧
      M.SuccessorOf S a ∧ Rd_fun_d .prod ω C ω P ∧ Rd_fun_d .prod S P S B ∧
        rd_closure_s.matrix_binary.toBinarySchema.denote (ρ.push a) C Wr ∧
          Pi_wit_d pg_filter_s C B D Wd ∧ M.mem w D ∧ Pi_wit_d pi_slice_s w D I Wi) ↔ _
  constructor
  · rintro ⟨T, a, _, h, _, c, _, ω, _, C, _, S, _, P, _, B, _, D, _, Wr, _, Wd, _, Wi, _, hw, ha, hω, hs, hp, hb, hr, hd, hwD, hi⟩
    exact ⟨a, h, c, ω, C, B, D, hw, ha, hω,
      (rd_closure_sat_l hKP.1 ρ a C).mp ((rd_closure_s.sat_l ρ a C).mpr ⟨Wr, hr⟩),
      ⟨S, P, hs, hp, hb⟩, (pi_wit_value_l pg_filter_s C B D).mp ⟨Wd, hd⟩, hwD,
      (pi_wit_value_l pi_slice_s w D I).mp ⟨Wi, hi⟩⟩
  · rintro ⟨a, h, c, ω, C, B, D, hw, ha, hω, hr, ⟨S, P, hs, hp, hb⟩, hd, hwD, hi⟩
    obtain ⟨Wr, hr⟩ := (rd_closure_s.sat_l ρ a C).mp ((rd_closure_sat_l hKP.1 ρ a C).mpr hr)
    obtain ⟨Wd, hd⟩ := (pi_wit_value_l pg_filter_s C B D).mpr hd
    obtain ⟨Wi, hi⟩ := (pi_wit_value_l pi_slice_s w D I).mpr hi
    obtain ⟨T, ht⟩ := kp_finite_cover_l hKP [a, h, c, ω, C, S, P, B, D, Wr, Wd, Wi]
    exact ⟨T, a, (ht a (by simp)).2, h, (ht h (by simp)).2, c, (ht c (by simp)).2, ω, (ht ω (by simp)).2,
      C, (ht C (by simp)).2, S, (ht S (by simp)).2, P, (ht P (by simp)).2, B, (ht B (by simp)).2,
      D, (ht D (by simp)).2, Wr, (ht Wr (by simp)).2, Wd, (ht Wd (by simp)).2, Wi, (ht Wi (by simp)).2,
      hw, ha, hω, hs, hp, hb, hr, hd, hwD, hi⟩

end YesMetaZFC.SetTheory.InnerModel
