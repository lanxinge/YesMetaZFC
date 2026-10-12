import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticSource
import YesMetaZFC.Model.SetTheory.Internal.TupleCode

/-! # 全高度弹性的实际内部程序

ZF 中按内部元数构造原程序；原变量先自动打包，源与类型都在公式内绑定。
语义读取中的 ZFC 用于实际超幂及支撑层枚举，不参与程序构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K₀" => fp_interpretation_l (ZF.models_kpi_l hZF)

private theorem st_ee_slots_l {ω w v d e b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hv : M.mem v b) (hd : M.mem d b) (he : M.mem e b)
    (hn : M.mem n ω) (hnb : M.MemberSubset n b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ (hZFC : M.Models ZFC) ν μ X Y Z c R c' R' κ δ K S s f,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → Ep_source_d hZF ω κ K Z S → Smem_d Q c X R → Smem_d Q c' Y R' →
      Fn0_d n X s → M.mem δ X → M.IsSetFunctionFromTo Q f ω Y →
      (∀ i x, M.mem i n → (M.PairMember Q i x s ↔ M.PairMember Q i x f)) →
      M.PairMember Q w ω f → M.PairMember Q v n f → M.PairMember Q d δ f → M.PairMember Q e κ f →
        (Satisfies_d Q ω c' a f ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c Z S) := by
  let φ : Formula 1 5 := ee_realized_m (.bound 4) (.bound 1) (.bound 2) (.bound 3) .newest
  obtain ⟨a, m, G, u, form, compile⟩ := st_tuple_bind_l hZF hω hb hw hv hn hnb φ
    (ee_realized_closed_l _ _ _ _ _ rfl rfl rfl rfl rfl)
    (Fin.cases e (Fin.cases d (Fin.cases v (fun _ => w)))) (Fin.cases he (Fin.cases hd (Fin.cases hv (fun _ => hw))))
  refine ⟨a, m, G, u, form, fun hZFC ν μ X Y Z c R c' R' κ δ K S s f hV hW hs hZ hδ hωδ hκδ
    source lower upper fs point fn orig fw fv fd fe => ?_⟩
  have hωY := fn.output_mem_of_pairMember fw
  have sfn := fn0_function_l (ZF.modelsKP hZF) fs
  let ρ : Env (smdl_structure_l Q (R := R') upper.1.2.1) 4 :=
    ⟨Fin.cases ⟨κ, fn.output_mem_of_pairMember fe⟩ (Fin.cases ⟨δ, fn.output_mem_of_pairMember fd⟩
      (Fin.cases ⟨n, fn.output_mem_of_pairMember fv⟩ (fun _ => ⟨ω, hωY⟩))), fun _ => ⟨ω, hωY⟩⟩
  have graph h (hh : M.IsSetFunctionFromTo K₀ h n X)
      (same : ∀ i x, M.mem i n → (M.PairMember K₀ i x h ↔ M.PairMember Q i x f)) : Sx_graph_d Q K₀ s h :=
    fun i x => ⟨fun hx => (orig i x (hh.input_mem_of_pairMember hx)).mpr ((same i x (hh.input_mem_of_pairMember hx)).mp hx),
      fun hx => (same i x (sfn.input_mem_of_pairMember hx)).mpr ((orig i x (sfn.input_mem_of_pairMember hx)).mp hx)⟩
  have atom (h : (smdl_structure_l Q (R := R') upper.1.2.1).Domain) (same : Sx_graph_d Q K₀ s h.val) :
      Formula.satisfies (ρ.push h) φ ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c Z S := by
    let η : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 5 := ⟨(ρ.push h).bound, (ρ.push h).free⟩
    exact (smem_formula_l Q upper _ φ η).symm.trans (ee_realized_source_l hZFC hω hV hW hs hωY η
      (.bound 4) (.bound 1) (.bound 2) (.bound 3) .newest rfl source hZ hδ hωδ hκδ lower hn fs point same)
  refine (compile ν μ X Y c' R' f upper ρ hV hW hs hωY fn fw fv
    (Fin.cases fe (Fin.cases fd (Fin.cases fv (fun _ => fw))))).trans ⟨?_, ?_⟩
  · rintro ⟨h, hh, same, truth⟩
    exact (atom h (graph h.val hh same)).mp truth
  · intro truth
    obtain ⟨h, hh, same⟩ := fn_recode_l Q K₀ hZF sfn
    have hδν := ZF.v_ordinal_height_l hZF hV hδ.1 point
    have hων := fun i hi => (v_ordinal_l Q hV).transitive δ hδν i (hδ.1.transitive ω hωδ i hi)
    have hHY := (ZF.v_successor_l Q hZF hV hW hs h).mpr (fp_function_rank_l Q hZF hω hV hων
      (fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i (hω.transitive hZF n hn i hi))) hh)
    exact ⟨⟨h, hHY⟩, hh, fun i x hi => (same i x).trans (orig i x hi), (atom ⟨h, hHY⟩ same).mpr truth⟩

/-- 构造只依赖内部 n；同一个原程序在全部合法后继秩层中精确读取全高度条件。 -/
theorem st_ee_build_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ v d e a m G u, M.SuccessorOf v n ∧ M.SuccessorOf d v ∧ M.SuccessorOf e d ∧ Sformula_d Q ω a m G u ∧
      ∀ (hZFC : M.Models ZFC) ν μ X Y Z c R c' R' κ δ K S s f,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → Ep_source_d hZF ω κ K Z S → Smem_d Q c X R → Smem_d Q c' Y R' →
      Fn0_d n X s → M.mem δ X → M.IsSetFunctionFromTo Q f ω Y →
      (∀ i x, M.mem i n → (M.PairMember Q i x s ↔ M.PairMember Q i x f)) →
      M.PairMember Q n ω f → M.PairMember Q v n f → M.PairMember Q d δ f → M.PairMember Q e κ f →
        (Satisfies_d Q ω c' a f ↔ Ee_realized_d (ZFC.models_zf_l hZFC) ω κ δ n s c Z S) := by
  obtain ⟨v, hv, hvω⟩ := hω.1.2 n hn
  obtain ⟨d, hd, hdω⟩ := hω.1.2 v hvω
  obtain ⟨e, he, heω⟩ := hω.1.2 d hdω
  obtain ⟨b, hb, hbω⟩ := hω.1.2 e heω
  have de := (hω.members_areOrdinals hZF e heω).transitive d he.predecessor_mem
  have vd := (hω.members_areOrdinals hZF d hdω).transitive v hd.predecessor_mem
  have eb := (hω.members_areOrdinals hZF b hbω).transitive e hb.predecessor_mem
  have nb := eb n (de n (vd n hv.predecessor_mem))
  obtain ⟨a, m, G, u, form, read⟩ := st_ee_slots_l hZF hω hbω nb (eb v (de v hd.predecessor_mem))
    (eb d he.predecessor_mem) hb.predecessor_mem hn ((hω.members_areOrdinals hZF b hbω).transitive n nb)
  exact ⟨v, d, e, a, m, G, u, hv, hd, he, form, read⟩

def Ee_stretch_read_d (ω n v d e z : M.Domain) : Prop := ∀ ν μ X Y Z c R c' R' κ δ K S s f,
    V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ →
    M.mem ω δ → M.mem κ δ → Ep_source_d hZF ω κ K Z S → Smem_d Q c X R → Smem_d Q c' Y R' →
    Fn0_d n X s → M.mem δ X → M.IsSetFunctionFromTo Q f ω Y →
    (∀ i x, M.mem i n → (Rd_entry_d i x s ↔ Rd_entry_d i x f)) →
    Rd_entry_d n ω f → Rd_entry_d v n f → Rd_entry_d d δ f → Rd_entry_d e κ f →
      (Sc_sat_d Q ω c' z f ↔ Ee_realized_d hZF ω κ δ n s c Z S)

/-- 伸展程序的自由参数全是内部自然数；κ、δ 及赋值只在读取时代入。 -/
structure Ee_stretch_program_d (ω n v d e z : M.Domain) : Prop where
  finite : M.mem n ω
  next_finite : M.mem v ω
  point_finite : M.mem d ω
  critical_finite : M.mem e ω
  natural : M.mem z ω
  next : M.SuccessorOf v n
  point : M.SuccessorOf d v
  critical : M.SuccessorOf e d
  read : ∀ hZFC : M.Models ZFC, Ee_stretch_read_d (ZFC.models_zf_l hZFC) ω n v d e z

include hZF in
theorem ee_stretch_program_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ v d e z, Ee_stretch_program_d ω n v d e z := by
  obtain ⟨v, d, e, a, m, G, u, hv, hd, he, form, compile⟩ := st_ee_build_l hZF hω hn
  obtain ⟨z, code⟩ := sc_num_exists_l Q hZF hω form
  have finite {a b} (ha : M.mem a ω) (succ : M.SuccessorOf b a) : M.mem b ω := by
    obtain ⟨b', hb', hbω⟩ := hω.1.2 a ha
    exact Structure.SuccessorOf.eq hZF.1 hb' succ ▸ hbω
  exact ⟨v, d, e, z, hn, finite hn hv, finite (finite hn hv) hd, finite (finite (finite hn hv) hd) he,
    sc_num_natural_l Q hZF hω code, hv, hd, he,
    fun hZFC ν μ X Y Z c R c' R' κ δ K S s f hX hY succ hZ hδ hwδ hkδ source lower upper tuple point fn old hw hn hd he =>
      (sc_sat_decode_l Q hZF hω code).trans
        (compile hZFC ν μ X Y Z c R c' R' κ δ K S s f hX hY succ hZ hδ hwδ hkδ source lower upper tuple point fn old hw hn hd he)⟩

end YesMetaZFC.SetTheory.LargeCardinal
