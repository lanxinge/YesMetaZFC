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
  obtain ⟨a₀, m₀, G₀, u₀, form₀, tuple⟩ := st_tuple_build_l hZF hω hb hw hv hn hnb
  obtain ⟨j, hj, hjω⟩ := hω.1.2 b hb
  let φ : Formula 1 6 := tf_type_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ (tf_type_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl))
    (Fin.cases t (Fin.cases e (Fin.cases b (Fin.cases v (Fin.cases d (fun _ => w)))))) hjω
    (Fin.cases ((hj t).mpr (Or.inl ht)) (Fin.cases ((hj e).mpr (Or.inl he))
      (Fin.cases hj.predecessor_mem (Fin.cases ((hj v).mpr (Or.inl hv))
        (Fin.cases ((hj d).mpr (Or.inl hd)) (fun _ => (hj w).mpr (Or.inl hw))))))) form₀.2.1
  obtain ⟨m₂, G₂, u₂, a₂, both⟩ := sfm_and_l Q hZF hω add.program (add.span u₀ form₀.2.2) add.root
  obtain ⟨m, G, u, a₃, ex⟩ := sfm_ex_l Q hZF hω a₂.program hb a₂.root
  obtain ⟨a, ha⟩ := (Q).total G u
  have form : Sformula_d Q ω a m G u := ⟨ha, a₃.program, a₃.root⟩
  refine ⟨a, m, G, u, form, fun ν μ X Y Z c R c' R' δ U D s f z hV hW hs hZ hδ hωδ
    lower upper fs point constants pool hU fn orig fw fv fd fe ft => ?_⟩
  have hωY := fn.output_mem_of_pairMember fw
  have hDZ := pool.rank_mem_l hZF hω hZ hδ (ZF.v_ordinal_mem_l Q hZF hZ hωδ) hn hU
  have sfn := fn0_function_l (ZF.modelsKP hZF) fs
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF Q ω Y
  have hf := (hE f).mpr fn
  have read h (hh : M.mem h Y) f₁ (update : Senv_update_d Q f b h f₁) :
      Ssat_d Q Y R' E G₂ m₂ u₂ f₁ ↔ M.IsSetFunctionFromTo K h n X ∧
        Sx_graph_d Q K s h ∧ Tt_truth_d Q ω c n s δ D z := by
    have fn₁ := update.function_l Q fn hb hh
    have hf₁ := (hE f₁).mpr fn₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    have fw₁ := (old w ω hw).mp fw
    have fv₁ := (old v n hv).mp fv
    have fd₁ := (old d δ hd).mp fd
    have fe₁ := (old e D he).mp fe
    have ft₁ := (old t z ht).mp ft
    have fh := (update.2 b h).mpr (Or.inl ⟨rfl, rfl⟩)
    have tuples := (add.sat_l Q hZF form₀.2.1 form₀.2.2 Y R' E f₁).symm.trans
      ((satisfies_decode_l Q hZF.1 upper.1 form₀ hE).symm.trans
        (tuple ν μ X Y c' R' f₁ h hV hW hs hωY upper fn₁ fw₁ fv₁ fh))
    have graph (hs' : M.IsSetFunctionFromTo K h n X) :
        (∀ i x, M.mem i n → (M.PairMember K i x h ↔ M.PairMember Q i x f₁)) ↔ Sx_graph_d Q K s h := by
      constructor
      · intro same i x
        exact ⟨fun hx => (orig i x (hs'.input_mem_of_pairMember hx)).mpr
          ((old i x (hnb i (hs'.input_mem_of_pairMember hx))).mpr ((same i x (hs'.input_mem_of_pairMember hx)).mp hx)),
          fun hx => (same i x (sfn.input_mem_of_pairMember hx)).mpr
            ((old i x (hnb i (sfn.input_mem_of_pairMember hx))).mp ((orig i x (sfn.input_mem_of_pairMember hx)).mp hx))⟩
      · intro same i x hi
        exact (same i x).trans ((orig i x hi).trans (old i x (hnb i hi)))
    have atom (same : Sx_graph_d Q K s h) : Ssat_d Q Y R' E G₁ m₁ u₁ f₁ ↔ Tt_truth_d Q ω c n s δ D z := by
      let η : Env (smdl_structure_l Q (R := R') upper.1.2.1) 6 :=
        ⟨Fin.cases ⟨z, fn.output_mem_of_pairMember ft⟩ (Fin.cases ⟨D, fn.output_mem_of_pairMember fe⟩
          (Fin.cases ⟨h, hh⟩ (Fin.cases ⟨n, fn.output_mem_of_pairMember fv⟩
            (Fin.cases ⟨δ, fn.output_mem_of_pairMember fd⟩ (fun _ => ⟨ω, hωY⟩))))), fun _ => ⟨h, hh⟩⟩
      exact (compile Y R' upper.1.2.1 E hE f₁ hf₁ η
        (Fin.cases ft₁ (Fin.cases fe₁ (Fin.cases fh (Fin.cases fv₁ (Fin.cases fd₁ (fun _ => fw₁))))))).trans
          ((source_core_sat_l φ η).trans ((smem_formula_l Q upper _ φ
            (⟨η.bound, η.free⟩ : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 6)).symm.trans
              (tf_type_source_l hZF hω hV hW hs hωY _ (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
                rfl hZ hδ hωδ lower hn fs point constants pool hDZ same)))
    refine (both Y R' E f₁ hf₁).trans ⟨?_, ?_⟩
    · rintro ⟨tuple', truth⟩
      obtain ⟨hh', eq⟩ := tuples.mp tuple'
      have same := (graph hh').mp eq
      exact ⟨hh', same, (atom same).mp truth⟩
    · rintro ⟨hh', same, truth⟩
      exact ⟨tuples.mpr ⟨hh', (graph hh').mpr same⟩, (atom same).mpr truth⟩
  refine (satisfies_decode_l Q hZF.1 upper.1 form hE).trans ((ex Y R' E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨h, f₁, hh, update, truth⟩
    exact ((read h hh f₁ update).mp truth).2.2
  · intro truth
    obtain ⟨h, hh, same⟩ := fn_recode_l Q K hZF sfn
    have hδν := ZF.v_ordinal_height_l hZF hV hδ.1 point
    have hων := fun i hi => (v_ordinal_l Q hV).transitive δ hδν i (hδ.1.transitive ω hωδ i hi)
    have hHY := (ZF.v_successor_l Q hZF hV hW hs h).mpr (fp_function_rank_l Q hZF hω hV hων
      (fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i (hω.transitive hZF n hn i hi))) hh)
    obtain ⟨f₁, update, _⟩ := senv_update_exists_l Q hZF fn hb hHY
    exact ⟨h, f₁, hHY, update, (read h hHY f₁ update).mpr ⟨hh, same, truth⟩⟩

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
