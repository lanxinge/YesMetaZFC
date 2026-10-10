import YesMetaZFC.Model.SetTheory.Internal.TupleCode
import YesMetaZFC.Model.SetTheory.Internal.FlatTypeRead

/-! # 从原变量列读取完整前驱类型的内部公式

将任意内部有限变量列的图编译与完整类型矩阵合取，再存在量化元组图。
公式码只依赖变量位置及元数；实现元组、背景秩层与类型候选均在语义端输入。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

private theorem st_type_slots_l {ω w v d e t b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hv : M.mem v b) (hd : M.mem d b) (he : M.mem e b) (ht : M.mem t b)
    (hn : M.mem n ω) (hnb : M.MemberSubset n b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ ν μ X Y Z c R c' R' δ U D s f z,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ → M.mem ω δ →
      Smem_d Q c X R → Smem_d Q c' Y R' → Fn0_d n X s → M.mem δ X → M.MemberSubset U X →
      Tt_pool_d Q ω n U D → M.mem U Z → M.IsSetFunctionFromTo Q f ω Y →
      (∀ i x, M.mem i n → (M.PairMember Q i x s ↔ M.PairMember Q i x f)) →
      M.PairMember Q w ω f → M.PairMember Q v n f → M.PairMember Q d δ f →
      M.PairMember Q e D f → M.PairMember Q t z f →
        (Satisfies_d Q ω c' a f ↔ Tt_truth_d Q ω c n s δ D z) := by
  let φ : Formula 1 6 := tf_type_m (.bound 5) (.bound 4) (.bound 3) .newest (.bound 2) (.bound 1)
  obtain ⟨a, m, G, u, form, compile⟩ := st_tuple_bind_l hZF hω hb hw hv hn hnb φ
    (tf_type_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl)
    (Fin.cases t (Fin.cases e (Fin.cases v (Fin.cases d (fun _ => w)))))
    (Fin.cases ht (Fin.cases he (Fin.cases hv (Fin.cases hd (fun _ => hw)))))
  refine ⟨a, m, G, u, form, fun ν μ X Y Z c R c' R' δ U D s f z hV hW hs hZ hδ hωδ
    lower upper fs point constants pool hU fn orig fw fv fd fe ft => ?_⟩
  have hωY := fn.output_mem_of_pairMember fw
  have hDZ := pool.rank_mem_l hZF hω hZ hδ (ZF.v_ordinal_mem_l Q hZF hZ hωδ) hn hU
  have sfn := fn0_function_l (ZF.modelsKP hZF) fs
  let ρ : Env (smdl_structure_l Q (R := R') upper.1.2.1) 5 :=
    ⟨Fin.cases ⟨z, fn.output_mem_of_pairMember ft⟩ (Fin.cases ⟨D, fn.output_mem_of_pairMember fe⟩
      (Fin.cases ⟨n, fn.output_mem_of_pairMember fv⟩ (Fin.cases ⟨δ, fn.output_mem_of_pairMember fd⟩
        (fun _ => ⟨ω, hωY⟩)))), fun _ => ⟨ω, hωY⟩⟩
  have graph h (hh : M.IsSetFunctionFromTo K h n X)
      (same : ∀ i x, M.mem i n → (M.PairMember K i x h ↔ M.PairMember Q i x f)) : Sx_graph_d Q K s h :=
    fun i x => ⟨fun hx => (orig i x (hh.input_mem_of_pairMember hx)).mpr ((same i x (hh.input_mem_of_pairMember hx)).mp hx),
      fun hx => (same i x (sfn.input_mem_of_pairMember hx)).mpr ((orig i x (sfn.input_mem_of_pairMember hx)).mp hx)⟩
  have atom (h : (smdl_structure_l Q (R := R') upper.1.2.1).Domain) (same : Sx_graph_d Q K s h.val) :
      Formula.satisfies (ρ.push h) φ ↔ Tt_truth_d Q ω c n s δ D z := by
    let η : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 6 := ⟨(ρ.push h).bound, (ρ.push h).free⟩
    exact (smem_formula_l Q upper _ φ η).symm.trans
      (tf_type_source_l hZF hω hV hW hs hωY η (.bound 5) (.bound 4) (.bound 3) .newest (.bound 2) (.bound 1)
        rfl hZ hδ hωδ lower hn fs point constants pool hDZ same)
  refine (compile ν μ X Y c' R' f upper ρ hV hW hs hωY fn fw fv
    (Fin.cases ft (Fin.cases fe (Fin.cases fv (Fin.cases fd (fun _ => fw)))))).trans ⟨?_, ?_⟩
  · rintro ⟨h, hh, same, truth⟩
    exact (atom h (graph h.val hh same)).mp truth
  · intro truth
    obtain ⟨h, hh, same⟩ := fn_recode_l Q K hZF sfn
    have hδν := ZF.v_ordinal_height_l hZF hV hδ.1 point
    have hων := fun i hi => (v_ordinal_l Q hV).transitive δ hδν i (hδ.1.transitive ω hωδ i hi)
    have hHY := (ZF.v_successor_l Q hZF hV hW hs h).mpr (fp_function_rank_l Q hZF hω hV hων
      (fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i (hω.transitive hZF n hn i hi))) hh)
    exact ⟨⟨h, hHY⟩, hh, fun i x hi => (same i x).trans (orig i x hi), (atom ⟨h, hHY⟩ same).mpr truth⟩

/-- 自动分配 ω、元数、δ、查询域与候选类型五个槽；无需外部元组图或编译证书。 -/
theorem st_type_build_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ v d e t a m G u, M.SuccessorOf v n ∧ M.SuccessorOf d v ∧ M.SuccessorOf e d ∧ M.SuccessorOf t e ∧
      Sformula_d Q ω a m G u ∧ ∀ ν μ X Y Z c R c' R' δ U D s f z,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ → M.mem ω δ →
      Smem_d Q c X R → Smem_d Q c' Y R' → Fn0_d n X s → M.mem δ X → M.MemberSubset U X →
      Tt_pool_d Q ω n U D → M.mem U Z → M.IsSetFunctionFromTo Q f ω Y →
      (∀ i x, M.mem i n → (M.PairMember Q i x s ↔ M.PairMember Q i x f)) →
      M.PairMember Q n ω f → M.PairMember Q v n f → M.PairMember Q d δ f →
      M.PairMember Q e D f → M.PairMember Q t z f →
        (Satisfies_d Q ω c' a f ↔ Tt_truth_d Q ω c n s δ D z) := by
  obtain ⟨v, hv, hvω⟩ := hω.1.2 n hn
  obtain ⟨d, hd, hdω⟩ := hω.1.2 v hvω
  obtain ⟨e, he, heω⟩ := hω.1.2 d hdω
  obtain ⟨t, ht, htω⟩ := hω.1.2 e heω
  obtain ⟨b, hb, hbω⟩ := hω.1.2 t htω
  have et := (hω.members_areOrdinals hZF t htω).transitive e ht.predecessor_mem
  have de := (hω.members_areOrdinals hZF e heω).transitive d he.predecessor_mem
  have vd := (hω.members_areOrdinals hZF d hdω).transitive v hd.predecessor_mem
  have tb := (hω.members_areOrdinals hZF b hbω).transitive t hb.predecessor_mem
  have nb := tb n (et n (de n (vd n hv.predecessor_mem)))
  obtain ⟨a, m, G, u, form, read⟩ := st_type_slots_l hZF hω hbω nb
    (tb v (et v (de v hd.predecessor_mem))) (tb d (et d he.predecessor_mem))
    (tb e ht.predecessor_mem) hb.predecessor_mem hn ((hω.members_areOrdinals hZF b hbω).transitive n nb)
  exact ⟨v, d, e, t, a, m, G, u, hv, hd, he, ht, form, read⟩

end YesMetaZFC.SetTheory.Internal
