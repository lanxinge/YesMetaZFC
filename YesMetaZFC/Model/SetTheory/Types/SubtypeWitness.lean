import YesMetaZFC.Model.SetTheory.Types.MoveQuote
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.FlatPairing.RankObjects
import YesMetaZFC.Model.SetTheory.Types.LowerSource

/-! # 原类型元组的有限排列

排列图保留原 Kuratowski 编码，元组采用平坦图。矩阵只在给定有限定义域及
对象域上比较坐标；从实际排列与实际赋值直接构造排列后的元组。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tp_perm_d (K : FlatPairing.convention.Interpretation M) (m A π g h : M.Domain) : Prop :=
  ∀ i, M.mem i m → ∀ x, M.mem x A →
    (M.PairMember K i x h ↔ ∃ j, M.mem j m ∧ Rd_entry_d i j π ∧ M.PairMember K j x g)

def tp_perm0_m {d} (ω m A π g h : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜m⌝ₛ, ∀ x ∈ ⌜A⌝ₛ,
  ⌜fp_entry0_m⌝ₚ(⌜ω⌝ₛ, i, x, ⌜h⌝ₛ) ↔
    (∃ j ∈ ⌜m⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, j, ⌜π⌝ₛ) ∧ ⌜fp_entry0_m⌝ₚ(⌜ω⌝ₛ, j, x, ⌜g⌝ₛ))⟫
derive_free_closed tp_perm0_m

theorem tp_perm0_delta_l {d} (ω m A π g h : Term d) : (tp_perm0_m ω m A π g h).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (fp_entry0_delta_l ..) (.existsMem _ (.conj (rd_entry0_delta_l ..) (fp_entry0_delta_l ..)))))

theorem tp_perm0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω m A π g h : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (tp_perm0_m ω m A π g h) ↔
      Tp_perm_d (fp_interpretation_l hKPi) (m.eval ρ) (A.eval ρ) (π.eval ρ) (g.eval ρ) (h.eval ρ) := by
  have left i x := fp_entry0_sat_l hKPi ((ρ.push i).push x) ω.weaken.weaken
    (.newest : Term (d+1)).weaken .newest h.weaken.weaken (by simpa only [Definitional.Term.eval_weaken] using hω)
  have right i x j := fp_entry0_sat_l hKPi (((ρ.push i).push x).push j) ω.weaken.weaken.weaken
    .newest (.newest : Term (d+2)).weaken g.weaken.weaken.weaken (by simpa only [Definitional.Term.eval_weaken] using hω)
  simp only [tp_perm0_m, Tp_perm_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, left, right,
    rd_entry0_sat_l (KPi.models_iff_l.mp hKPi).1.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

/-- 给定的有限排列产生实际元组图；构造只用 ZF，不选择任何外部序列。 -/
theorem tp_permute_l {ω m A π g : M.Domain} (hω : M.IsOmega ω) (hm : M.mem m ω)
    (hp : M.IsSetBijectionFromTo Q π m m) (hg : M.IsSetFunctionFromTo K g ω A) :
    ∃ h, M.IsSetFunctionFromTo K h m A ∧ Tp_perm_d K m A π g h := by
  let ρ : Env M 3 := ⟨Fin.cases π (Fin.cases g (fun _ => ω)), fun _ => g⟩
  let φ : BinarySchema 3 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (fp_entry0_m (.bound 5) .newest (.bound 1) (.bound 4))) }
  have sat i x : φ.denote ρ i x ↔ ∃ j, Rd_entry_d i j π ∧ M.PairMember K j x g := by
    have entry j := fp_entry0_sat_l (ZF.models_kpi_l hZF) (((ρ.push i).push x).push j)
      (.bound 5) .newest (.bound 1) (.bound 4) hω
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1,
      entry]
    rfl
  obtain ⟨h, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF K φ ρ
    (fun i hi => by
      obtain ⟨j, hj, hij⟩ := hp.1.1.2.2 i hi
      obtain ⟨x, _, hx⟩ := hg.2.2 j (hω.transitive (ZF.modelsKP hZF) m hm j hj)
      exact ⟨x, (sat i x).mpr ⟨j, hij, hx⟩⟩)
    (fun i _ x y hx hy => by
      obtain ⟨j, hij, hjx⟩ := (sat i x).mp hx
      obtain ⟨k, hik, hky⟩ := (sat i y).mp hy
      exact hg.1.2 j x y hjx (hp.1.1.1.2 i k j hik hij ▸ hky))
    (fun i x _ hx => by obtain ⟨j, _, hjx⟩ := (sat i x).mp hx; exact hg.output_mem_of_pairMember hjx)
  refine ⟨h, fn, fun i hi x _ => (graph i x).trans ((and_iff_right hi).trans ((sat i x).trans ?_))⟩
  exact ⟨fun ⟨j, hij, hjx⟩ => ⟨j, hp.1.1.output_mem_of_pairMember hij, hij, hjx⟩,
    fun ⟨j, _, hij, hjx⟩ => ⟨j, hij, hjx⟩⟩

/-- 自然数域上的原排列图属于 Vω，因而属于每个包含 ω 的外层。 -/
theorem tp_permutation_rank_l {ω η Y m π : M.Domain} (hω : M.IsOmega ω) (hY : V_d Q η Y)
    (hw : M.mem ω Y) (hm : M.mem m ω) (hp : M.IsSetBijectionFromTo Q π m m) : M.mem π Y := by
  obtain ⟨W, hW⟩ := ZF.v_exists_l Q hZF (hω.isOrdinal (ZF.modelsKP hZF))
  have hπ := v_relation_mem_l Q hW (hω.isLimitOrdinal (ZF.modelsKP hZF)) (ZF.v_ordinal_mem_l Q hZF hW hm)
    (fn0_of_function_l (ZF.modelsKP hZF) hp.1.1).1
  exact v_transitive_l Q hY W
    (ZF.v_mem_l Q hZF hW hY (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal (ZF.modelsKP hZF)) hw)) π hπ

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型句子的秩内语义

句子绑定较低秩层、任意内部有限元组和实际排列。前 n 个变量由平坦前缀码
指定；候选 w 仍以原查询编码保存，全部真值由通用较低层读取公式核验。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_below_d (hZF : M.Models ZF) (ω δ m U D w n p η : M.Domain) : Prop :=
  let Q := kp_pair_l (ZF.modelsKP hZF)
  let K := fp_interpretation_l (ZF.models_kpi_l hZF)
  ∃ ν A c R s g h π, M.mem ν η ∧ V_d Q ν A ∧ Smem_d Q c A R ∧
    Tt_realized_d Q ω c A R m s δ U D w ∧ M.IsSetFunctionFromTo K g ω A ∧
    M.IsSetFunctionFromTo K h m A ∧ Sx_graph_d Q K s h ∧ Fs_code_d K ω A g n p ∧
    M.IsSetBijectionFromTo Q π m m ∧ Tp_perm_d K m A π g h

def ts_guard_m {d} (ω κ τ m : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜κ⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜τ⌝ₛ) ∧ ⌜τ⌝ₛ ∈ ⌜κ⌝ₛ ∧ ⌜m⌝ₛ ∈ ⌜ω⌝ₛ⟫
derive_free_closed ts_guard_m

theorem ts_guard_source_l {Y : M.Domain} (ht : M.TransitiveSet Y) (ny : Nonempty {x // M.mem x Y})
    (hKP : M.Models KP) {d} (ρ : Env (rt_model_l Y ny) d) (ω κ τ m : Term d) :
    Formula.satisfies ρ (ts_guard_m ω κ τ m) ↔ M.IsLimitOrdinal (κ.eval ρ).val ∧
      M.IsLimitOrdinal (τ.eval ρ).val ∧ M.mem (τ.eval ρ).val (κ.eval ρ).val ∧ M.mem (m.eval ρ).val (ω.eval ρ).val := by
  simp only [ts_guard_m, Formula.satisfies_conj_iff, Formula.satisfies_isLimitOrdinal_iff,
    rt_limit_l ht ny hKP, Formula.satisfies_mem_iff]
  rfl

def ts_below_s : UnarySchema 7 where
  body := set[8] ⟪⌜ts_guard_m⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, ⌜(.bound 6 : Term 8)⌝ₛ,
    ⌜(.bound 5 : Term 8)⌝ₛ, ⌜(.bound 3 : Term 8)⌝ₛ) ∧
    ⌜(.bound 4 : Term 8)⌝ₛ ⊆ ⌜(.bound 3 : Term 8)⌝ₛ ∧
    (∃ ν A C g h π, ⌜v_m FlatPairing.convention⌝ₚ(ν, A) ∧
      ⌜v_m FlatPairing.convention⌝ₚ(⌜(.bound 6 : Term 8)⌝ₛ, C) ∧
      ⌜(.bound 5 : Term 8)⌝ₛ ∈ A ∧ ⌜(.bound 2 : Term 8)⌝ₛ ∈ A ∧
      ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(g, ⌜(.bound 7 : Term 8)⌝ₛ, A) ∧
      ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(h, ⌜(.bound 3 : Term 8)⌝ₛ, A) ∧
      ⌜fs_code_m (𝒞 := FlatPairing.convention)⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, A, g,
        ⌜(.bound 4 : Term 8)⌝ₛ, ⌜(.newest : Term 8)⌝ₛ) ∧
      ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(π, ⌜(.bound 3 : Term 8)⌝ₛ, ⌜(.bound 3 : Term 8)⌝ₛ) ∧
      ⌜tp_perm0_m⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, ⌜(.bound 3 : Term 8)⌝ₛ, A, π, g, h) ∧
      ⌜tf_lower_type_m⌝ₚ(⌜(.bound 7 : Term 8)⌝ₛ, C, ⌜(.bound 5 : Term 8)⌝ₛ,
        ⌜(.bound 3 : Term 8)⌝ₛ, A, h, ⌜(.bound 2 : Term 8)⌝ₛ, ⌜(.bound 1 : Term 8)⌝ₛ))⟫

def ts_below_m {d} (ω κ τ n m δ w p : Term d) : Formula 1 d :=
  pred_m ts_below_s (Fin.cases w (Fin.cases δ (Fin.cases m (Fin.cases n (Fin.cases τ
    (Fin.cases κ (fun _ => ω))))))) p

@[simp] theorem ts_below_closed_l {d} (ω κ τ n m δ w p : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (ht : τ.freeSupport = []) (hn : n.freeSupport = [])
    (hm : m.freeSupport = []) (hd : δ.freeSupport = []) (hu : w.freeSupport = []) (hp : p.freeSupport = []) :
    (ts_below_m ω κ τ n m δ w p).FreeClosed :=
  pred_m_freeClosed ts_below_s _ _ (Fin.cases hu (Fin.cases hd (Fin.cases hm
    (Fin.cases hn (Fin.cases ht (Fin.cases hk (fun _ => hw))))))) hp

variable (hZF : M.Models ZF) {ω η Y : M.Domain} (hω : M.IsOmega ω)
  (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "ny" => Nonempty.intro (Subtype.mk ω hωY)
local notation "N" => rt_model_l Y ny
local notation "J" => fp_rank_interpretation_l Q hZF hω hY hωY

include hω hY in
private theorem ts_below_values_l (κ τ n m δ w p : (N).Domain) {B U D : M.Domain}
    (hκ : M.IsLimitOrdinal κ.val) (hτ : M.IsLimitOrdinal τ.val) (hτκ : M.mem τ.val κ.val) (hm : M.mem m.val ω)
    (hB : V_d Q τ.val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = τ.val) (pool : Tt_pool_d Q ω m.val U D) :
    Formula.satisfies (⟨Fin.cases p (Fin.cases w (Fin.cases δ (Fin.cases m (Fin.cases n (Fin.cases τ
      (Fin.cases κ (fun _ => ⟨ω, hωY⟩))))))), fun _ => p⟩ : Env N 8) ts_below_s.body ↔
        M.MemberSubset n.val m.val ∧ Ts_below_d hZF ω δ.val m.val U D w.val n.val p.val η := by
  let ρ : Env N 8 := ⟨Fin.cases p (Fin.cases w (Fin.cases δ (Fin.cases m (Fin.cases n (Fin.cases τ
    (Fin.cases κ (fun _ => ⟨ω, hωY⟩))))))), fun _ => p⟩
  have ht := v_transitive_l Q hY
  have hωκ := ordinal_down_l (ZF.modelsKP hZF) (hω.isOrdinal (ZF.modelsKP hZF)) hκ.1 (hω.subset_limitOrdinal (ZF.modelsKP hZF) hτ) hτκ
  have bound {ν A} (ha : V_d Q ν A) (hτA : M.mem τ.val A) : M.MemberSubset ω ν :=
    fun i hi => (v_ordinal_l Q ha).transitive τ.val (ZF.v_ordinal_height_l hZF ha hτ.1 hτA) i
      (hω.subset_limitOrdinal (ZF.modelsKP hZF) hτ i hi)
  have perm (ν A C g h π : (N).Domain) :
      Formula.satisfies ((((((ρ.push ν).push A).push C).push g).push h).push π)
        (tp_perm0_m (.bound 13) (.bound 9) (.bound 4) .newest (.bound 2) (.bound 1)) ↔
      Tp_perm_d K m.val A.val π.val g.val h.val :=
    (rt_model_delta_l ht ny (tp_perm0_delta_l ..) _).trans
      (tp_perm0_sat_l (ZF.models_kpi_l hZF) _ (.bound 13) (.bound 9) (.bound 4) .newest (.bound 2) (.bound 1) hω)
  have types (ν A C g h π : (N).Domain) {c R s : M.Domain} (ha : V_d Q ν.val A.val) (hc : V_d Q κ.val C.val)
      (hτA : M.mem τ.val A.val) (hd : M.mem δ.val A.val) (model : Smem_d Q c A.val R)
      (tuple : Fn0_d m.val A.val s) (agree : Sx_graph_d Q K s h.val) :=
    tf_lower_type_source_l hZF hω hY hωY ((((((ρ.push ν).push A).push C).push g).push h).push π)
      (.bound 13) (.bound 3) (.bound 11) (.bound 9) (.bound 4) (.bound 1) (.bound 8) (.bound 7) rfl
      hc hκ hωκ hτκ ha (bound ha hτA) hτA hB constants pool model hm tuple hd agree
  have sub : (N).MemberSubset n m ↔ M.MemberSubset n.val m.val :=
    ⟨fun h i hi => h ⟨i, ht n.val n.property i hi⟩ hi, fun h i hi => h i.val hi⟩
  have guard : Formula.satisfies ρ (ts_guard_m (.bound 7) (.bound 6) (.bound 5) (.bound 3)) :=
    (ts_guard_source_l ht ny (ZF.modelsKP hZF) ρ _ _ _ _).mpr ⟨hκ, hτ, hτκ, hm⟩
  simp only [ts_below_s, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff, v_sat_l J (rt_model_ext_l hZF.1 ht ny), Formula.satisfies_mem_iff,
    Formula.satisfies_isFunctionFromTo_iff J (rt_model_ext_l hZF.1 ht ny), fs_code_sat_l J (rt_model_ext_l hZF.1 ht ny),
    rt_bijection_formula_l ht ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF))]
  refine (and_iff_right guard).trans (and_congr sub ⟨?_, ?_⟩)
  · rintro ⟨ν, A, C, g, h, π, ha, hc, hτA, hd, fg, fh, prefixCode, bij, permuted, truth⟩
    have va := (rt_fp_v_l Q hZF hω hY hωY ν A).mp ha
    have vc := (rt_fp_v_l Q hZF hω hY hωY κ C).mp hc
    have fg := (rt_fp_function_from_l Q hZF hω hY hωY g ⟨ω, hωY⟩ A).mp fg
    have fh := (rt_fp_function_from_l Q hZF hω hY hωY h m A).mp fh
    obtain ⟨s, fs, agree⟩ := fn_recode_l K Q hZF fh
    have same : Sx_graph_d Q K s h.val := fun i x => (agree i x).symm
    obtain ⟨c, R, model⟩ := smdl_membership_l Q hZF ⟨δ.val, hd⟩
    have ba := ZF.v_mono_l Q hZF hB va ((v_ordinal_l Q va).transitive τ.val (ZF.v_ordinal_height_l hZF va hτ.1 hτA))
    have ua : M.MemberSubset U A.val := fun x hx => ((constants x).mp hx).elim (ba x) (fun eq => eq.symm ▸ hτA)
    exact ⟨ν.val, A.val, c, R, s, g.val, h.val, π.val,
      ZF.v_ordinal_height_l hZF hY (v_ordinal_l Q va) ν.property, va, model,
      ⟨model.1, hm, fn0_of_function_l (ZF.modelsKP hZF) fs, hd, ua, pool,
        (types ν A C g h π va vc hτA hd model (fn0_of_function_l (ZF.modelsKP hZF) fs) same).mp truth⟩,
      fg, fh, same, (rt_fs_code_l Q hZF hω hY hωY A g n p va (bound va hτA)).mp prefixCode, bij, (perm ν A C g h π).mp permuted⟩
  · rintro ⟨ν, A, c, R, s, g, h, π, hν, ha, model, type, fg, fh, agree, prefixCode, bij, permuted⟩
    have hτA := type.constants τ.val ((constants τ.val).mpr (Or.inr rfl))
    have hων := bound ha hτA
    have nat : M.MemberSubset ω A := fun i hi => ZF.v_ordinal_mem_l Q hZF ha (hων i hi)
    obtain ⟨C, hc⟩ := ZF.v_exists_l Q hZF hκ.1
    let ν' : (N).Domain := ⟨ν, ZF.v_ordinal_mem_l Q hZF hY hν⟩
    let A' : (N).Domain := ⟨A, ZF.v_mem_l Q hZF ha hY hν⟩
    let C' : (N).Domain := ⟨C, ZF.v_mem_l Q hZF hc hY (ZF.v_ordinal_height_l hZF hY hκ.1 κ.property)⟩
    let g' : (N).Domain := ⟨g, v_subset_mem_l Q hY A'.property (fp_function_rank_l Q hZF hω ha hων nat fg)⟩
    let h' : (N).Domain := ⟨h, v_subset_mem_l Q hY A'.property
      (fp_function_rank_l Q hZF hω ha hων (fun i hi => nat i (hω.transitive (ZF.modelsKP hZF) m.val hm i hi)) fh)⟩
    let π' : (N).Domain := ⟨π, tp_permutation_rank_l hZF hω hY hωY hm bij⟩
    exact ⟨ν', A', C', g', h', π', (rt_fp_v_l Q hZF hω hY hωY ν' A').mpr ha,
      (rt_fp_v_l Q hZF hω hY hωY κ C').mpr hc, hτA, type.point,
      (rt_fp_function_from_l Q hZF hω hY hωY g' ⟨ω, hωY⟩ A').mpr fg,
      (rt_fp_function_from_l Q hZF hω hY hωY h' m A').mpr fh,
      (rt_fs_code_l Q hZF hω hY hωY A' g' n p ha hων).mpr prefixCode, bij, (perm ν' A' C' g' h' π').mpr permuted,
      (types ν' A' C' g' h' π' ha hc hτA type.point model type.tuple agree).mpr type.truth⟩

include hω hY in
theorem ts_below_source_l {d} (ρ : Env N d) (v κ τ n m δ w p : Term d) (hv : v.eval ρ = ⟨ω, hωY⟩)
    {B U D : M.Domain} (hκ : M.IsLimitOrdinal (κ.eval ρ).val) (hτ : M.IsLimitOrdinal (τ.eval ρ).val)
    (hτκ : M.mem (τ.eval ρ).val (κ.eval ρ).val) (hm : M.mem (m.eval ρ).val ω)
    (hB : V_d Q (τ.eval ρ).val B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = (τ.eval ρ).val)
    (pool : Tt_pool_d Q ω (m.eval ρ).val U D) : Formula.satisfies ρ (ts_below_m v κ τ n m δ w p) ↔
      M.MemberSubset (n.eval ρ).val (m.eval ρ).val ∧
        Ts_below_d hZF ω (δ.eval ρ).val (m.eval ρ).val U D (w.eval ρ).val (n.eval ρ).val (p.eval ρ).val η := by
  have env : (Definitional.Env.substitute ρ (Fin.cases p (Fin.cases w (Fin.cases δ (Fin.cases m (Fin.cases n (Fin.cases τ
      (Fin.cases κ (fun _ => v))))))))).bound =
      (⟨Fin.cases (p.eval ρ) (Fin.cases (w.eval ρ) (Fin.cases (δ.eval ρ) (Fin.cases (m.eval ρ) (Fin.cases (n.eval ρ)
        (Fin.cases (τ.eval ρ) (Fin.cases (κ.eval ρ) (fun _ => ⟨ω, hωY⟩))))))), fun _ => p.eval ρ⟩ : Env N 8).bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => hv))))))) i
  exact (Formula.satisfies_bind _ _ _).trans ((Formula.closed_env_l ts_below_s.body ts_below_s.freeClosed env).trans
    (ts_below_values_l hZF hω hY hωY (κ.eval ρ) (τ.eval ρ) (n.eval ρ) (m.eval ρ) (δ.eval ρ) (w.eval ρ) (p.eval ρ)
      hκ hτ hτκ hm hB constants pool))

theorem ts_below_guard_l {Y : M.Domain} (ht : M.TransitiveSet Y) (ne : Nonempty {x // M.mem x Y})
    (hKP : M.Models KP) {d} (ρ : Env (rt_model_l Y ne) d) (v κ τ n m δ w p : Term d)
    (h : Formula.satisfies ρ (ts_below_m v κ τ n m δ w p)) :
    M.IsLimitOrdinal (κ.eval ρ).val ∧ M.IsLimitOrdinal (τ.eval ρ).val ∧
      M.mem (τ.eval ρ).val (κ.eval ρ).val ∧ M.mem (m.eval ρ).val (v.eval ρ).val := by
  have h := (Formula.satisfies_bind _ _ _).mp h
  exact (ts_guard_source_l ht ne hKP _ (.bound 7) (.bound 6) (.bound 5) (.bound 3)).mp h.1

theorem Ts_below_d.mono_l {ω δ m U D w n p η θ : M.Domain} (h : Ts_below_d hZF ω δ m U D w n p η)
    (sub : M.MemberSubset η θ) : Ts_below_d hZF ω δ m U D w n p θ := by
  obtain ⟨ν, A, c, R, s, g, f, π, hν, rest⟩ := h
  exact ⟨ν, A, c, R, s, g, f, π, sub ν hν, rest⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型的完整实现见证

较低层中的全赋值提供有限额外变量，实际排列给出 w 的实现顺序。
平坦前缀码相等精确等价于原 n 个变量逐项一致，因此不损失任何原变量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_at_d (hZF : M.Models ZF) (ω δ n s m U D w ν : M.Domain) : Prop :=
  let Q := kp_pair_l (ZF.modelsKP hZF)
  let K := fp_interpretation_l (ZF.models_kpi_l hZF)
  ∃ A c R r g h π, V_d Q ν A ∧ Smem_d Q c A R ∧
    Tt_realized_d Q ω c A R m r δ U D w ∧ M.IsSetFunctionFromTo K g ω A ∧
    M.IsSetFunctionFromTo K h m A ∧ Sx_graph_d Q K r h ∧
    (∀ i x, M.mem i n → (Rd_entry_d i x s ↔ M.PairMember K i x g)) ∧
    M.IsSetBijectionFromTo Q π m m ∧ Tp_perm_d K m A π g h

def Ts_real_d (hZF : M.Models ZF) (ω δ n s m U D w η : M.Domain) : Prop :=
  ∃ ν, M.mem ν η ∧ Ts_at_d hZF ω δ n s m U D w ν

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem ts_prefix_l {ω η Y δ n s m U D w g : M.Domain} (hω : M.IsOmega ω) (hY : V_d Q η Y)
    (hn : M.mem n ω) (hwU : M.mem ω U) (fg : M.IsSetFunctionFromTo K g ω Y)
    (same : ∀ i x, M.mem i n → (Rd_entry_d i x s ↔ M.PairMember K i x g)) :
    (∃ p, M.mem p Y ∧ Fs_code_d K ω Y g n p ∧ Ts_below_d hZF ω δ m U D w n p η) ↔
      Ts_real_d hZF ω δ n s m U D w η := by
  constructor
  · rintro ⟨p, _, code, ν, A, c, R, r, f, h, π, hν, hA, model, type, ff, fh, graph, cp, bij, perm⟩
    have sub := ZF.v_mono_l Q hZF hA hY ((v_ordinal_l Q hY).transitive ν hν)
    have ff' : M.IsSetFunctionFromTo K f ω Y := ⟨ff.1, ff.2.1, fun i hi =>
      (ff.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩
    have equal := (code.prefix_l K hZF hω fg ff' (cp.mono_l K sub)).mp rfl
    exact ⟨ν, hν, A, c, R, r, f, h, π, hA, model, type, ff, fh, graph,
      fun i x hi => (same i x hi).trans (equal i x hi), bij, perm⟩
  · rintro ⟨ν, hν, A, c, R, r, f, h, π, hA, model, type, ff, fh, graph, orig, bij, perm⟩
    have sub := ZF.v_mono_l Q hZF hA hY ((v_ordinal_l Q hY).transitive ν hν)
    have hwA := type.constants ω hwU
    have hων := (v_ordinal_l Q hA).transitive ω (ZF.v_ordinal_height_l hZF hA (hω.isOrdinal (ZF.modelsKP hZF)) hwA)
    obtain ⟨p, hp, cp⟩ := fp_finite_rank_l Q hZF hω hA hων ff hn
    have ff' : M.IsSetFunctionFromTo K f ω Y := ⟨ff.1, ff.2.1, fun i hi =>
      (ff.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩
    have hωη := (v_ordinal_l Q hY).transitive ω (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal (ZF.modelsKP hZF)) (sub ω hwA))
    obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hY hωη fg
    exact ⟨p, sub p hp, (cp.mono_l K sub).transport_l K hZF hω ff' fg trace
      (fun i x hi => (orig i x hi).symm.trans (same i x hi)),
      ν, A, c, R, r, f, h, π, hν, hA, model, type, ff, fh, graph, cp, bij, perm⟩

/-- 同一个完整类型有恒等排列实例，所有赋值图均由原集合论构造。 -/
theorem ts_at_self_l {ω ν A c R n s δ U D w : M.Domain} (hω : M.IsOmega ω)
    (hA : V_d Q ν A) (model : Smem_d Q c A R) (type : Tt_realized_d Q ω c A R n s δ U D w) :
    Ts_at_d hZF ω δ n s n U D w ν := by
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l Q hZF (fn0_function_l (ZF.modelsKP hZF) type.tuple) type.point
  obtain ⟨g, fg, agree⟩ := fn_recode_l Q K hZF ff
  obtain ⟨h, fh, graph⟩ := fn_recode_l Q K hZF (fn0_function_l (ZF.modelsKP hZF) type.tuple)
  have orig i x (hi : M.mem i n) : Rd_entry_d i x s ↔ M.PairMember K i x g :=
    (show Rd_entry_d i x s ↔ Rd_entry_d i x f from
      ⟨fun hx => (fill.2 i x).mpr ⟨hω.transitive (ZF.modelsKP hZF) n type.finite i hi, Or.inl ⟨hi, hx⟩⟩,
        fun hx => ((fill.2 i x).mp hx).2.elim And.right (fun h => (h.1 hi).elim)⟩).trans (agree i x).symm
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have sat i j : φ.denote ρ i j ↔ j = i := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨π, fn, entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Q φ ρ (source := n) (target := n)
    (fun i _ => ⟨i, (sat i i).mpr rfl⟩)
    (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
    (fun i j hi hj => ((sat i j).mp hj).symm ▸ hi)
  have id i j : Rd_entry_d i j π ↔ M.mem i n ∧ j = i := (entries i j).trans (and_congr_right fun _ => sat i j)
  have bij : M.IsSetBijectionFromTo Q π n n :=
    ⟨⟨fn, fun i j x hx hy => ((id i x).mp hx).2.symm.trans ((id j x).mp hy).2⟩,
      fun x hx => ⟨x, hx, (id x x).mpr ⟨hx, rfl⟩⟩⟩
  refine ⟨A, c, R, s, g, h, π, hA, model, type, fg, fh, graph, orig, bij, ?_⟩
  intro i hi x _
  refine ⟨fun hx => ⟨i, hi, (id i i).mpr ⟨hi, rfl⟩, (orig i x hi).mp ((graph i x).mp hx)⟩, ?_⟩
  rintro ⟨j, _, ij, jx⟩
  have eq := ((id i j).mp ij).2
  subst j
  exact (graph i x).mpr ((orig i x hi).mpr jx)

end YesMetaZFC.SetTheory.Internal
