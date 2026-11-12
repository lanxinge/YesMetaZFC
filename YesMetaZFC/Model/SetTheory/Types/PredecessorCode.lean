import YesMetaZFC.Model.SetTheory.Types.FlatTypePredecessor
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Internal.TupleCode

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
  have trans := v_transitive_l Q hW
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
    (fun i hi => nat i (hω.transitive (ZF.modelsKP hZF) (n.eval ρ) hn i hi)) hh)
  have hZY := ZF.v_mem_l Q hZF hZ hW ((hs (δ.eval ρ)).mpr (Or.inl hδν))
  have hωZ := ZF.v_ordinal_mem_l Q hZF hZ hωδ
  have hDZ := pool.rank_mem_l (ZF.modelsKP hZF) hω hZ hδ hωZ hn hU
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
    let u : N.Domain := ⟨t.eval ρ, trans Z hZY (t.eval ρ) (v_subset_mem_l Q hZ hDZ sub)⟩
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

/-! ## 从原变量列读取完整前驱类型的内部公式

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
  have hDZ := pool.rank_mem_l (ZF.modelsKP hZF) hω hZ hδ (ZF.v_ordinal_mem_l Q hZF hZ hωδ) hn hU
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
      (fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i (hω.transitive (ZF.modelsKP hZF) n hn i hi))) hh)
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
  have et := (hω.members_areOrdinals (ZF.modelsKP hZF) t htω).transitive e ht.predecessor_mem
  have de := (hω.members_areOrdinals (ZF.modelsKP hZF) e heω).transitive d he.predecessor_mem
  have vd := (hω.members_areOrdinals (ZF.modelsKP hZF) d hdω).transitive v hd.predecessor_mem
  have tb := (hω.members_areOrdinals (ZF.modelsKP hZF) b hbω).transitive t hb.predecessor_mem
  have nb := tb n (et n (de n (vd n hv.predecessor_mem)))
  obtain ⟨a, m, G, u, form, read⟩ := st_type_slots_l hZF hω hbω nb
    (tb v (et v (de v hd.predecessor_mem))) (tb d (et d he.predecessor_mem))
    (tb e ht.predecessor_mem) hb.predecessor_mem hn ((hω.members_areOrdinals (ZF.modelsKP hZF) b hbω).transitive n nb)
  exact ⟨v, d, e, t, a, m, G, u, hv, hd, he, ht, form, read⟩

end YesMetaZFC.SetTheory.Internal
