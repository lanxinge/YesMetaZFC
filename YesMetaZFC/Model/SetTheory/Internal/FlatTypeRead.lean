import YesMetaZFC.Model.SetTheory.Internal.FlatTypePredecessor
import YesMetaZFC.Model.SetTheory.Internal.TypeRank

/-! # 原完整前驱类型的自动公式接口

原查询域与候选类型保持原编码。平坦元组由实际重编码构造；
一个元组同时读取所有候选类型，候选的秩界由查询域自动给出。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tf_type_local_m {d} (Y ω δ n h D t : Term d) : Formula 1 d :=
  .conj (Formula.subset t D)
    (lr_rel_m (tf_type_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 6)) Y
      (Fin.cases t (Fin.cases D (Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => ω)))))))

@[simp] theorem tf_type_local_closed_l {d} (Y ω δ n h D t : Term d)
    (hY : Y.freeSupport = []) (hω : ω.freeSupport = []) (hδ : δ.freeSupport = [])
    (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hD : D.freeSupport = []) (ht : t.freeSupport = []) :
    (tf_type_local_m Y ω δ n h D t).FreeClosed := by
  simp only [tf_type_local_m, Definitional.Formula.FreeClosed]
  exact ⟨by simp -implicitDefEqProofs [Formula.subset, Definitional.Formula.FreeClosed, ht, hD],
    lr_rel_closed_l _ (tf_type_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl) Y _ hY
    (Fin.cases ht (Fin.cases hD (Fin.cases hh (Fin.cases hn (Fin.cases hδ (fun _ => hω))))))⟩

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

/-- 对任意候选集合精确成立；不要求它预先属于后继秩层或已经是类型。 -/
theorem tf_type_rank_l {d} (ρ : Env M d) (Y ω δ n h D t : Term d) {ν μ X Z c R s U : M.Domain}
    (hω : M.IsOmega (ω.eval ρ)) (hV : V_d Q ν X) (hW : V_d Q μ (Y.eval ρ)) (hs : M.SuccessorOf μ ν)
    (hZ : V_d Q (δ.eval ρ) Z) (hδ : M.IsLimitOrdinal (δ.eval ρ)) (hωδ : M.mem (ω.eval ρ) (δ.eval ρ))
    (hm : Smem_d Q c X R) (hn : M.mem (n.eval ρ) (ω.eval ρ)) (tuple : Fn0_d (n.eval ρ) X s)
    (point : M.mem (δ.eval ρ) X) (constants : M.MemberSubset U X)
    (pool : Tt_pool_d Q (ω.eval ρ) (n.eval ρ) U (D.eval ρ)) (hU : M.mem U Z)
    (hh : M.IsSetFunctionFromTo K (h.eval ρ) (n.eval ρ) X) (agree : Sx_graph_d Q K s (h.eval ρ)) :
    Formula.satisfies ρ (tf_type_local_m Y ω δ n h D t) ↔
      Tt_truth_d Q (ω.eval ρ) c (n.eval ρ) s (δ.eval ρ) (D.eval ρ) (t.eval ρ) := by
  have trans := ZF.v_transitive_l Q hZF hW
  have hδν := ZF.v_ordinal_height_l hZF hV hδ.1 point
  have hων : M.MemberSubset (ω.eval ρ) ν := fun i hi =>
    (v_ordinal_l Q hV).transitive (δ.eval ρ) hδν i (hδ.1.transitive (ω.eval ρ) hωδ i hi)
  have nat : M.MemberSubset (ω.eval ρ) X := fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i hi)
  have pow := ZF.v_successor_l Q hZF hV hW hs
  have hXY := (pow X).mpr (fun _ h => h)
  have hd := trans X hXY (δ.eval ρ) point
  have hw := trans (δ.eval ρ) hd (ω.eval ρ) hωδ
  have hnY := trans (ω.eval ρ) hw (n.eval ρ) hn
  have hH := (pow (h.eval ρ)).mpr (fp_function_rank_l Q hZF hω hV hων
    (fun i hi => nat i (hω.transitive hZF (n.eval ρ) hn i hi)) hh)
  have hZY := ZF.v_mem_l Q hZF hZ hW ((hs (δ.eval ρ)).mpr (Or.inl hδν))
  have hωZ := ZF.v_ordinal_mem_l Q hZF hZ hωδ
  have hDZ := pool.rank_mem_l hZF hω hZ hδ hωZ hn hU
  have hDY := trans Z hZY (D.eval ρ) hDZ
  let nz : Nonempty {x // M.mem x (Y.eval ρ)} := ⟨⟨ω.eval ρ, hw⟩⟩
  let N := rt_model_l (Y.eval ρ) nz
  let w : N.Domain := ⟨ω.eval ρ, hw⟩
  let a : N.Domain := ⟨δ.eval ρ, hd⟩
  let k : N.Domain := ⟨n.eval ρ, hnY⟩
  let f : N.Domain := ⟨h.eval ρ, hH⟩
  let B : N.Domain := ⟨D.eval ρ, hDY⟩
  let φ := tf_type_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 6)
  -- 外层子集条件为任意候选自动提供所属秩；源内矩阵再核验全部查询。
  have read (sub : M.MemberSubset (t.eval ρ) (D.eval ρ)) :
      Formula.satisfies ρ (lr_rel_m φ Y (Fin.cases t (Fin.cases D (Fin.cases h (Fin.cases n
        (Fin.cases δ (fun _ => ω))))))) ↔ Tt_truth_d Q (ω.eval ρ) c (n.eval ρ) s (δ.eval ρ) (D.eval ρ) (t.eval ρ) := by
    let u : N.Domain := ⟨t.eval ρ, trans Z hZY (t.eval ρ) (ZF.v_subset_mem_l Q hZF hZ hDZ sub)⟩
    let η : Env N 6 := ⟨Fin.cases u (Fin.cases B (Fin.cases f (Fin.cases k (Fin.cases a (fun _ => w))))), fun _ => f⟩
    exact (sc_relative_sat_l trans nz φ (tf_type_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl)
      η ρ Y (Fin.cases t (Fin.cases D (Fin.cases h (Fin.cases n (Fin.cases δ (fun _ => ω)))))) rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))).trans
        (tf_type_source_l hZF hω hV hW hs hw η (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest rfl
          hZ hδ hωδ hm hn tuple point constants pool hDZ agree)
  simp only [tf_type_local_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff]
  exact ⟨fun ⟨sub, truth⟩ => (read sub).mp truth, fun truth => by
    have sub := fun p hp => ((truth p).mp hp).1
    exact ⟨sub, (read sub).mpr truth⟩⟩

/-- 实际构造一份平坦元组，使同一原公式识别全部原完整类型候选。 -/
theorem tt_predecessor_formula_l {ω δ ν μ X Y Z c R n s U D : M.Domain}
    (hω : M.IsOmega ω) (hV : V_d Q ν X) (hW : V_d Q μ Y) (hs : M.SuccessorOf μ ν)
    (hZ : V_d Q δ Z) (hδ : M.IsLimitOrdinal δ) (hωδ : M.mem ω δ)
    (hm : Smem_d Q c X R) (hn : M.mem n ω) (tuple : Fn0_d n X s) (point : M.mem δ X)
    (constants : M.MemberSubset U X) (pool : Tt_pool_d Q ω n U D) (hU : M.mem U Z) :
    ∃ h, M.IsSetFunctionFromTo K h n X ∧ Sx_graph_d Q K s h ∧ ∀ t,
      (Formula.satisfies (⟨Fin.cases t (Fin.cases D (Fin.cases h (Fin.cases n
        (Fin.cases δ (Fin.cases ω (fun _ => Y)))))), fun _ => h⟩ : Env M 7)
          (tf_type_local_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) ↔
        Tt_truth_d Q ω c n s δ D t) := by
  obtain ⟨h, hh, agree⟩ := fn_recode_l Q K hZF (fn0_function_l (ZF.modelsKP hZF) tuple)
  exact ⟨h, hh, agree, fun t => tf_type_rank_l hZF _ _ _ _ _ _ _ _
    hω hV hW hs hZ hδ hωδ hm hn tuple point constants pool hU hh agree⟩

end YesMetaZFC.SetTheory.Internal
