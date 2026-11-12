import YesMetaZFC.Model.SetTheory.Types.LowerSource
import YesMetaZFC.Model.SetTheory.Types.FlatTypePredecessor
import YesMetaZFC.Model.SetTheory.Internal.TupleCode

/-! # 前一秩层中 κ 型的完整原公式

公式自行求出 Vδ、Vκ、常量域和全部查询域；输入仅有 ω、κ、δ、元数、
平坦元组及类型候选。解码、查询域与真值始终保持原编码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tf_kappa_s : UnarySchema 5 where
  body := set[6] ⟪∃ A C, ⌜sv_last_m⌝ₚ(A) ∧ ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 3 : Term 6)⌝ₛ, C) ∧
    ⌜tf_lower_type_m⌝ₚ(⌜(.bound 5 : Term 6)⌝ₛ, C, ⌜(.bound 4 : Term 6)⌝ₛ,
      ⌜(.bound 2 : Term 6)⌝ₛ, A, ⌜(.bound 1 : Term 6)⌝ₛ, ⌜(.bound 3 : Term 6)⌝ₛ, ⌜(.newest : Term 6)⌝ₛ)⟫
def tf_kappa_m {d} (ω κ δ n h t : Term d) : Formula 1 d :=
  pred_m tf_kappa_s (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => ω))))) t
@[simp] theorem tf_kappa_closed_l {d} (ω κ δ n h t : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hd : δ.freeSupport = [])
    (hn : n.freeSupport = []) (hh : h.freeSupport = []) (ht : t.freeSupport = []) :
    (tf_kappa_m ω κ δ n h t).FreeClosed :=
  pred_m_freeClosed tf_kappa_s _ _ (Fin.cases hh (Fin.cases hn (Fin.cases hd (Fin.cases hk (fun _ => hw))))) ht

variable (hZF : M.Models ZF) {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
  (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) ν X) (hW : V_d (kp_pair_l (ZF.modelsKP hZF)) μ Y)
  (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N₀" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l Q hZF hω hW hωY

include hω hV hW hs in
private theorem tf_kappa_values_l (κ δ n h t : (N₀).Domain) {Z B U D c R s : M.Domain}
    (hZ : V_d Q δ.val Z) (hδ : M.IsLimitOrdinal δ.val) (hωδ : M.mem ω δ.val) (hκδ : M.mem κ.val δ.val)
    (hB : V_d Q κ.val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ.val)
    (pool : Tt_pool_d Q ω n.val U D) (hm : Smem_d Q c X R) (hn : M.mem n.val ω)
    (tuple : Fn0_d n.val X s) (point : M.mem δ.val X) (agree : Sx_graph_d Q K s h.val) :
    Formula.satisfies (⟨Fin.cases t (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ
      (fun _ => ⟨ω, hωY⟩))))), fun _ => h⟩ : Env N₀ 6) tf_kappa_s.body ↔ Tt_truth_d Q ω c n.val s δ.val D t.val := by
  let ρ : Env N₀ 6 := ⟨Fin.cases t (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ
    (fun _ => ⟨ω, hωY⟩))))), fun _ => h⟩
  have trans := v_transitive_l Q hW
  have hδν := ZF.v_ordinal_height_l hZF hV hδ.1 point
  have hκν := (v_ordinal_l Q hV).transitive δ.val hδν κ.val hκδ
  have hκX := ZF.v_ordinal_mem_l Q hZF hV hκν
  have hων : M.MemberSubset ω ν := fun i hi =>
    (v_ordinal_l Q hV).transitive δ.val hδν i (hδ.1.transitive ω hωδ i hi)
  have types (A C : (N₀).Domain) (eq : A.val = X) (layer : V_d Q δ.val C.val) :=
    tf_lower_type_source_l hZF hω hW hωY ((ρ.push A).push C)
      (.bound 7) .newest (.bound 6) (.bound 4) (.bound 1) (.bound 3) (.bound 5) (.bound 2) rfl
      layer hδ hωδ hκδ (eq.symm ▸ hV) hων (eq.symm ▸ hκX) hB constants pool
      (eq.symm ▸ hm) hn (eq.symm ▸ tuple) (eq.symm ▸ point) agree
  simp only [tf_kappa_s, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sv_last_rank_l Q hZF hω hV hW hs hωY, v_sat_l J (rt_model_ext_l hZF.1 trans _),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨A, C, eq, layer, truth⟩
    exact (types A C eq ((rt_fp_v_l Q hZF hω hW hωY δ C).mp layer)).mp truth
  · intro truth
    let A : (N₀).Domain := ⟨X, (ZF.v_successor_l Q hZF hV hW hs X).mpr (fun _ h => h)⟩
    let C : (N₀).Domain := ⟨Z, ZF.v_mem_l Q hZF hZ hW ((hs δ.val).mpr (Or.inl hδν))⟩
    exact ⟨A, C, rfl, (rt_fp_v_l Q hZF hω hW hωY δ C).mpr hZ, (types A C rfl hZ).mpr truth⟩
include hω hV hW hs in
theorem tf_kappa_source_l {d} (ρ : Env N₀ d) (w κ δ n h t : Term d) (hw : w.eval ρ = ⟨ω, hωY⟩)
    {Z B U D c R s : M.Domain} (hZ : V_d Q (δ.eval ρ).val Z) (hδ : M.IsLimitOrdinal (δ.eval ρ).val)
    (hωδ : M.mem ω (δ.eval ρ).val) (hκδ : M.mem (κ.eval ρ).val (δ.eval ρ).val)
    (hB : V_d Q (κ.eval ρ).val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = (κ.eval ρ).val)
    (pool : Tt_pool_d Q ω (n.eval ρ).val U D) (hm : Smem_d Q c X R) (hn : M.mem (n.eval ρ).val ω)
    (tuple : Fn0_d (n.eval ρ).val X s) (point : M.mem (δ.eval ρ).val X)
    (agree : Sx_graph_d Q K s (h.eval ρ).val) : Formula.satisfies ρ (tf_kappa_m w κ δ n h t) ↔
      Tt_truth_d Q ω c (n.eval ρ).val s (δ.eval ρ).val D (t.eval ρ).val := by
  have env : (Definitional.Env.substitute ρ (Fin.cases t (Fin.cases h (Fin.cases n (Fin.cases δ (Fin.cases κ (fun _ => w))))))).bound =
      (⟨Fin.cases (t.eval ρ) (Fin.cases (h.eval ρ) (Fin.cases (n.eval ρ) (Fin.cases (δ.eval ρ)
        (Fin.cases (κ.eval ρ) (fun _ => ⟨ω, hωY⟩))))), fun _ => h.eval ρ⟩ : Env N₀ 6).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hw))))) i
  exact (Formula.satisfies_bind _ _ _).trans ((Formula.closed_env_l tf_kappa_s.body tf_kappa_s.freeClosed env).trans
    (tf_kappa_values_l hZF hω hV hW hs hωY (κ.eval ρ) (δ.eval ρ) (n.eval ρ) (h.eval ρ) (t.eval ρ)
      hZ hδ hωδ hκδ hB constants pool hm hn tuple point agree))

end YesMetaZFC.SetTheory.Internal

/-! ## 任意内部元数的 κ 型读取程序

统一元组绑定器消费固定 κ 型公式。常量域和查询域都在公式内部构造，
原变量之外只保留 ω、元数、δ、κ 与类型候选五个参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

private theorem st_kappa_slots_l {ω w v d e t b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hv : M.mem v b) (hd : M.mem d b) (he : M.mem e b) (ht : M.mem t b)
    (hn : M.mem n ω) (hnb : M.MemberSubset n b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ ν μ X Y Z c R c' R' κ δ B U D s f z,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → V_d Q κ B → (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) →
      Tt_pool_d Q ω n U D → Smem_d Q c X R → Smem_d Q c' Y R' → Fn0_d n X s → M.mem δ X →
      M.IsSetFunctionFromTo Q f ω Y → (∀ i x, M.mem i n → (M.PairMember Q i x s ↔ M.PairMember Q i x f)) →
      M.PairMember Q w ω f → M.PairMember Q v n f → M.PairMember Q d δ f → M.PairMember Q e κ f → M.PairMember Q t z f →
        (Satisfies_d Q ω c' a f ↔ Tt_truth_d Q ω c n s δ D z) := by
  let φ : Formula 1 6 := tf_kappa_m (.bound 5) (.bound 2) (.bound 4) (.bound 3) .newest (.bound 1)
  obtain ⟨a, m, G, u, form, compile⟩ := st_tuple_bind_l hZF hω hb hw hv hn hnb φ
    (tf_kappa_closed_l _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl)
    (Fin.cases t (Fin.cases e (Fin.cases v (Fin.cases d (fun _ => w)))))
    (Fin.cases ht (Fin.cases he (Fin.cases hv (Fin.cases hd (fun _ => hw)))))
  refine ⟨a, m, G, u, form, fun ν μ X Y Z c R c' R' κ δ B U D s f z hV hW hs hZ hδ hωδ hκδ
    hB constants pool lower upper fs point fn orig fw fv fd fe ft => ?_⟩
  have hωY := fn.output_mem_of_pairMember fw
  have sfn := fn0_function_l (ZF.modelsKP hZF) fs
  let ρ : Env (smdl_structure_l Q (R := R') upper.1.2.1) 5 :=
    ⟨Fin.cases ⟨z, fn.output_mem_of_pairMember ft⟩ (Fin.cases ⟨κ, fn.output_mem_of_pairMember fe⟩
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
      (tf_kappa_source_l hZF hω hV hW hs hωY η (.bound 5) (.bound 2) (.bound 4) (.bound 3) .newest (.bound 1)
        rfl hZ hδ hωδ hκδ hB constants pool lower hn fs point same)
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

/-- 只输入内部元数便实际构造程序及参数槽；无需把查询域当成公式参数。 -/
theorem st_kappa_build_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ v d e t a m G u, M.SuccessorOf v n ∧ M.SuccessorOf d v ∧ M.SuccessorOf e d ∧ M.SuccessorOf t e ∧
      Sformula_d Q ω a m G u ∧ ∀ ν μ X Y Z c R c' R' κ δ B U D s f z,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → V_d Q δ Z → M.IsLimitOrdinal δ →
      M.mem ω δ → M.mem κ δ → V_d Q κ B → (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) →
      Tt_pool_d Q ω n U D → Smem_d Q c X R → Smem_d Q c' Y R' → Fn0_d n X s → M.mem δ X →
      M.IsSetFunctionFromTo Q f ω Y → (∀ i x, M.mem i n → (M.PairMember Q i x s ↔ M.PairMember Q i x f)) →
      M.PairMember Q n ω f → M.PairMember Q v n f → M.PairMember Q d δ f → M.PairMember Q e κ f → M.PairMember Q t z f →
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
  obtain ⟨a, m, G, u, form, read⟩ := st_kappa_slots_l hZF hω hbω nb
    (tb v (et v (de v hd.predecessor_mem))) (tb d (et d he.predecessor_mem))
    (tb e ht.predecessor_mem) hb.predecessor_mem hn ((hω.members_areOrdinals (ZF.modelsKP hZF) b hbω).transitive n nb)
  exact ⟨v, d, e, t, a, m, G, u, hv, hd, he, ht, form, read⟩

end YesMetaZFC.SetTheory.Internal
