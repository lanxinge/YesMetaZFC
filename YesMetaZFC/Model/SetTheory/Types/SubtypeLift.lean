import YesMetaZFC.Model.SetTheory.Types.Minus
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.Model.SetTheory.Types.Embedding

/-! # 前驱算子的自然数矩阵

把已经核验的纯语法转换收集为 ω 上的实际关系。给定这张矩阵，
查询转换和类型逆像都是有界公式；初等映射因而可直接搬运整个算子。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tm_table_d (ω B : M.Domain) : Prop := M.IsSetRelationOn I B ω ∧
  ∀ z w, M.PairMember I z w B ↔ Tm_code_d I ω z w

theorem tm_table_exists_l (hZF : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω) : ∃ B, Tm_table_d I ω B := by
  let φ : BinarySchema 1 := { body := tm_code_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  obtain ⟨B, hB, val⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ ω
  have read z w : φ.denote ρ z w ↔ Tm_code_d I ω z w := tm_code_sat_l I hZF.1 ..
  refine ⟨B, hB, fun z w => (val z w).trans ⟨fun h => (read z w).mp h.2.2, ?_⟩⟩
  intro h
  have zw := h.natural_l I hZF hω
  exact ⟨zw.1, zw.2, (read z w).mpr h⟩

def tm_link0_m {d} (ω B p q : Term d) : Formula 1 d := set[d] ⟪
  ∃ z ∈ ⌜ω⌝ₛ, ∃ w ∈ ⌜ω⌝ₛ, ∃ a ∈ ⌜p⌝ₛ, ∃ e ∈ a,
    ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, z, e) ∧ ⌜kpair0_m⌝ₚ(⌜q⌝ₛ, w, e) ∧ ⌜rd_entry0_m⌝ₚ(z, w, ⌜B⌝ₛ)⟫
derive_free_closed tm_link0_m

theorem tm_link0_delta_l {d} (ω B p q : Term d) : (tm_link0_m ω B p q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..))))))

theorem tm_link0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω B p q : Term d)
    (hB : Tm_table_d (kp_pair_l hKP) (ω.eval ρ) (B.eval ρ)) :
    Formula.satisfies ρ (tm_link0_m ω B p q) ↔ Tm_query_d (kp_pair_l hKP) (ω.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [tm_link0_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, kpair0_sat_l hKP.1,
    rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨z, _, w, _, _, _, e, _, cp, cq, code⟩
    exact ⟨z, e, w, cp, cq, (hB.2 z w).mp code⟩
  · rintro ⟨z, e, w, cp, cq, code⟩
    have entry := (hB.2 z w).mpr code
    have zw := hB.1.2 z w entry
    obtain ⟨a, ha, he⟩ := (kpair_union_l M cp e).mpr (Or.inr rfl)
    exact ⟨z, zw.1, w, zw.2, a, ha, e, he, cp, cq, entry⟩

def tm_cut0_m {d} (ω B D t u : Term d) : Formula 1 d := set[d] ⟪
  ⌜u⌝ₛ ⊆ ⌜D⌝ₛ ∧ (∀ p ∈ ⌜D⌝ₛ,
    p ∈ ⌜u⌝ₛ ↔ (∃ q ∈ ⌜t⌝ₛ, ⌜tm_link0_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, p, q)))⟫
derive_free_closed tm_cut0_m

theorem tm_cut0_delta_l {d} (ω B D t u : Term d) : (tm_cut0_m ω B D t u).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (.existsMem _ (tm_link0_delta_l ..))))

theorem tm_cut0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω B D t u : Term d)
    (hB : Tm_table_d (kp_pair_l hKP) (ω.eval ρ) (B.eval ρ)) :
    Formula.satisfies ρ (tm_cut0_m ω B D t u) ↔
      Tm_minus_d (kp_pair_l hKP) (ω.eval ρ) (D.eval ρ) (t.eval ρ) (u.eval ρ) := by
  have link p q := tm_link0_sat_l hKP ((ρ.push p).push q) ω.weaken.weaken B.weaken.weaken
    (.newest : Term (d+1)).weaken .newest (by simpa only [Definitional.Term.eval_weaken] using hB)
  simp only [tm_cut0_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, link, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨sub, read⟩ p
    exact ⟨fun hp => ⟨sub p hp, ((read p (sub p hp)).mp hp).imp fun q h => ⟨h.2, h.1⟩⟩,
      fun ⟨hp, q, code, hq⟩ => (read p hp).mpr ⟨q, hq, code⟩⟩
  · intro read
    exact ⟨fun p hp => ((read p).mp hp).1, fun p hp => ⟨fun hu =>
      ((read p).mp hu).2.imp fun q h => ⟨h.2, h.1⟩, fun ⟨q, hq, code⟩ => (read p).mpr ⟨hp, q, code, hq⟩⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 前驱类型与实际初等像交换

限制代码的整张自然数矩阵属于源秩层，并由初等映射逐点固定。
有界逆像公式因此搬运全部目标查询，包括不在旧查询逐点像中的参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 整张限制代码矩阵属于源，并被逐点固定；类型逆像和子类型闭包共同使用它。 -/
theorem Smap_d.type_table_l {ω θ X R c Y S d j B : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (table : Tm_table_d I ω B) : Rd_entry_d B B j := by
  have trans := v_transitive_l I hX
  have hBX : M.mem B X := v_relation_mem_l I hX hθ hωX (fun p hp => by
    obtain ⟨z, w, code⟩ := table.1.1 p hp
    have zw := table.1.2 z w ⟨p, code, hp⟩
    exact ⟨z, zw.1, w, zw.2, code⟩)
  exact hj.fixed_relation_l hZF hω trans hY hm hn (hj.omega_l I hZF hω trans hY hm hn hωX)
    (hj.natural_l hZF hω trans hY hm hn hωX) hBX table.1

/-- 只要求源为包含 ω 的极限秩层；不增加不可达性、选择或目标模型性前提。 -/
theorem Smap_d.type_minus_l {ω θ X R c Y S d j D t u D' t' u' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hD : Rd_entry_d D D' j) (ht : Rd_entry_d t t' j) (hu : Rd_entry_d u u' j) :
    Tm_minus_d I ω D t u ↔ Tm_minus_d I ω D' t' u' := by
  obtain ⟨B, table⟩ := tm_table_exists_l I hZF hω
  have trans := v_transitive_l I hX
  have hωj := hj.omega_l I hZF hω trans hY hm hn hωX
  have hBj := hj.type_table_l hZF hω hX hθ hωX hY hm hn table
  let φ : Formula 1 5 := tm_cut0_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  let ρ : Env M 5 := ⟨Fin.cases u (Fin.cases t (Fin.cases D (Fin.cases B (fun _ => ω)))), fun _ => ω⟩
  let η : Env M 5 := ⟨Fin.cases u' (Fin.cases t' (Fin.cases D' (Fin.cases B (fun _ => ω)))), fun _ => ω⟩
  have tr := smap_delta_l I hZF hω trans hY hm hn hj φ
    (tm_cut0_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) (tm_cut0_delta_l ..) ρ η
    (Fin.cases hu (Fin.cases ht (Fin.cases hD (Fin.cases hBj (fun _ => hωj)))))
  exact ((tm_cut0_sat_l (ZF.modelsKP hZF) ρ (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest table).symm.trans tr).trans
    (tm_cut0_sat_l (ZF.modelsKP hZF) η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest table)

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型查询的有界闭包性质

只固定自然数程序码、列长度和 ω 的槽位；其余名字任意变化。
量词全部有界，故这条统一闭包性质可由实际成员满嵌入运输。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_up_d (I : kpair_convention_l.Interpretation M) (ω b v z N E D u : M.Domain) : Prop :=
  ∀ C, M.mem C E → Fn0_d b N C →
    (∃ e, M.mem e N ∧ KPair_d M e ω ω ∧ Rd_entry_d v e C) →
    ∀ p, M.mem p D → ∀ r, M.mem r D → KPair_d M p z C → Tm_query_d I ω p r → M.mem r u → M.mem p u

def ts_up0_m {d} (ω b v z B N E D u : Term d) : Formula 1 d := set[d] ⟪
  ∀ C ∈ ⌜E⌝ₛ, ⌜fn0_m⌝ₚ(⌜b⌝ₛ, ⌜N⌝ₛ, C) →
    (∃ e ∈ ⌜N⌝ₛ, ⌜kpair0_m⌝ₚ(e, ⌜ω⌝ₛ, ⌜ω⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜v⌝ₛ, e, C)) →
    ∀ p ∈ ⌜D⌝ₛ, ∀ r ∈ ⌜D⌝ₛ, ⌜kpair0_m⌝ₚ(p, ⌜z⌝ₛ, C) →
      ⌜tm_link0_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, p, r) → r ∈ ⌜u⌝ₛ → p ∈ ⌜u⌝ₛ⟫
derive_free_closed ts_up0_m

theorem ts_up0_delta_l {d} (ω b v z B N E D u : Term d) : (ts_up0_m ω b v z B N E D u).IsDelta0 :=
  .forallMem _ (.imp (fn0_delta_l ..) (.imp (.existsMem _ (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..)))
    (.forallMem _ (.forallMem _ (.imp (kpair0_delta_l ..) (.imp (tm_link0_delta_l ..) (.imp (.mem ..) (.mem ..))))))))

theorem ts_up0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω b v z B N E D u : Term d)
    (table : Tm_table_d (kp_pair_l hKP) (ω.eval ρ) (B.eval ρ)) :
    Formula.satisfies ρ (ts_up0_m ω b v z B N E D u) ↔
      Ts_up_d (kp_pair_l hKP) (ω.eval ρ) (b.eval ρ) (v.eval ρ) (z.eval ρ)
        (N.eval ρ) (E.eval ρ) (D.eval ρ) (u.eval ρ) := by
  have link C p r := tm_link0_sat_l hKP (((ρ.push C).push p).push r) ω.weaken.weaken.weaken B.weaken.weaken.weaken
    (Term.newest : Term (d+2)).weaken .newest (by simpa only [Definitional.Term.eval_weaken] using table)
  simp only [ts_up0_m, Ts_up_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1, link, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

theorem Ts_program_d.closure_l {ω n b a z ν μ X Y c R d S s δ U N E D u : M.Domain}
    (hω : M.IsOmega ω) {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (hX : V_d Q ν X) (hY : V_d Q μ Y) (hs : M.SuccessorOf μ ν)
    (lower : Smem_d Q c X R) (upper : Smem_d Q d Y S)
    (type : Tt_realized_d Q ω d Y S n s δ U D u)
    (tuple : Fn0_d n X s) (point : M.mem δ X) (constants : M.MemberSubset U X) (names : Tn_names_d n U N) :
    Ts_up_d Q ω b (σ 6) z N E D u := by
  intro C _ column ⟨e, _, codeω, edgeω⟩ p hp r _ pair tm hr
  have fc := fn0_function_l (ZF.modelsKP hZF) column
  have hz := sc_num_natural_l Q hZF hω prog.code
  obtain ⟨t, assign, ft⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) n prog.finite)
    tuple point constants names column
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l Q hZF (fn0_function_l (ZF.modelsKP hZF) ft) point
  have restrict := tm.sat_l hZF hω lower upper (v_transitive_l Q hY)
    (sr_top_power_l (ZF.v_successor_l Q hZF hX hY hs)) pair hz prog.length fc.2.1 assign fill
    (fn0_of_function_l (ZF.modelsKP hZF) ff)
  have decode : Tt_query_d Q ω c n s δ p ↔ Satisfies_d Q ω c a f :=
    (tt_query_decode_l Q (ZF.modelsKP hZF) pair hz prog.length fc.2.1 assign fill).trans
    (sc_sat_decode_l Q hZF hω prog.code)
  have truth := decode.mp (restrict.mpr ((type.truth r).mp hr).2)
  have fw : Rd_entry_d (σ 6) ω f := (fill.2 (σ 6) ω).mpr
    ⟨hω.transitive (ZF.modelsKP hZF) b prog.length (σ 6) (prog.slots 6),
      Or.inl ⟨fc.input_mem_of_pairMember edgeω, (assign.2 (σ 6) ω).mpr ⟨e, edgeω, Or.inr (Or.inr codeω)⟩⟩⟩
  have raised := prog.up_l hZF hω hX hY (fun x hx => (hs x).mpr (Or.inl hx)) lower upper ff fw truth
  exact (type.truth p).mpr ⟨hp, (tt_query_decode_l Q (ZF.modelsKP hZF) pair hz prog.length fc.2.1 assign fill).mpr
    ((sc_sat_decode_l Q hZF hω prog.code).mpr raised)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型闭包沿实际初等映射运输

先在实际源中构造整张限制代码矩阵；自然数及矩阵均被映射固定。
有界公式因而覆盖像查询域中的所有新名字列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.subtype_up_l {ω θ X R c Y S d j b v z N E D u N' E' D' u' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hY : M.TransitiveSet Y) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hj : Smap_d I ω c d X Y j) (hb : M.mem b ω) (hv : M.mem v ω) (hz : M.mem z ω)
    (hN : Rd_entry_d N N' j) (hE : Rd_entry_d E E' j) (hD : Rd_entry_d D D' j) (hu : Rd_entry_d u u' j) :
    Ts_up_d I ω b v z N E D u ↔ Ts_up_d I ω b v z N' E' D' u' := by
  obtain ⟨B, table⟩ := tm_table_exists_l I hZF hω
  have trans := v_transitive_l I hX
  have fixed := hj.natural_l hZF hω trans hY hm hn hωX
  have hωj := hj.omega_l I hZF hω trans hY hm hn hωX
  have hBj := hj.type_table_l hZF hω hX hθ hωX hY hm hn table
  let φ : Formula 1 9 := ts_up0_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4)
    (.bound 3) (.bound 2) (.bound 1) .newest
  let ρ : Env M 9 := ⟨Fin.cases u (Fin.cases D (Fin.cases E (Fin.cases N (Fin.cases B
    (Fin.cases z (Fin.cases v (Fin.cases b (fun _ => ω)))))))), fun _ => ω⟩
  let η : Env M 9 := ⟨Fin.cases u' (Fin.cases D' (Fin.cases E' (Fin.cases N' (Fin.cases B
    (Fin.cases z (Fin.cases v (Fin.cases b (fun _ => ω)))))))), fun _ => ω⟩
  have tr := smap_delta_l I hZF hω trans hY hm hn hj φ
    (ts_up0_m_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl) (ts_up0_delta_l ..) ρ η
    (Fin.cases hu (Fin.cases hD (Fin.cases hE (Fin.cases hN (Fin.cases hBj
      (Fin.cases (fixed z hz) (Fin.cases (fixed v hv) (Fin.cases (fixed b hb) (fun _ => hωj)))))))))
  exact ((ts_up0_sat_l (ZF.modelsKP hZF) ρ (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4)
    (.bound 3) (.bound 2) (.bound 1) .newest table).symm.trans tr).trans
    (ts_up0_sat_l (ZF.modelsKP hZF) η (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest table)

end YesMetaZFC.SetTheory.Internal

/-! ## 从前驱类型的像返回原类型的像

高处的实现只用于证明源类型的有界闭包性质。实际嵌入仅作用于低秩源；
目标中的新查询经同一闭包性质读取，不要求嵌入扩张到实现所在的高秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.subtype_minus_l {ω θ X R c Z S d j n b a z U D u w D' u' w' : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hZ : M.TransitiveSet Z) (hm : Smem_d I c X R) (hn : Smem_d I d Z S)
    (hj : Smap_d I ω c d X Z j) {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (hUX : M.mem U X) (hD : Rd_entry_d D D' j) (hu : Rd_entry_d u u' j) (hw : Rd_entry_d w w' j)
    (minus : Tm_minus_d I ω D u w)
    {ν μ A Y c₀ R₀ d₀ S₀ s δ : M.Domain} (hA : V_d I ν A) (hY : V_d I μ Y) (hs : M.SuccessorOf μ ν)
    (lower : Smem_d I c₀ A R₀) (upper : Smem_d I d₀ Y S₀) (type : Tt_realized_d I ω d₀ Y S₀ n s δ U D u)
    (tuple : Fn0_d n A s) (point : M.mem δ A) (constants : M.MemberSubset U A)
    {q C H : M.Domain} (pair : (I).Codes q z C) (column : Fn0_d b H C)
    (omega : ∃ e, KPair_d M e ω ω ∧ Rd_entry_d (σ 6) e C) : M.mem q w' → M.mem q u' := by
  have trans := v_transitive_l I hX
  have fixed := hj.natural_l hZF hω trans hZ hm hn hωX
  obtain ⟨U', _, hU⟩ := hj.1.1.2.2 U hUX
  obtain ⟨N, E, N', E', names, _, _, hN, hE, _, sequences, product⟩ :=
    hj.type_frame_l hZF hω hX hθ hωX hZ hm hn prog.finite (fixed n prog.finite) hUX hU hD type.pool
  have closed := prog.closure_l hZF hω hA hY hs lower upper type tuple point constants names (E := E)
  have image := (hj.subtype_up_l hZF hω hX hθ hωX hZ hm hn prog.length
    (hω.transitive (ZF.modelsKP hZF) b prog.length (σ 6) (prog.slots 6)) (sc_num_natural_l I hZF hω prog.code)
    hN hE hD hu).mp closed
  have pred := (hj.type_minus_l hZF hω hX hθ hωX hZ hm hn hD hu hw).mp minus
  have sub := (hj.subset_l hZF hω trans hZ hm hn hu hD).mp (fun p hp => ((type.truth p).mp hp).1)
  intro hq
  obtain ⟨hqD, r, code, hr⟩ := (pred q).mp hq
  have hqZ := hZ D' (hj.1.1.output_mem_of_pairMember hD) q hqD
  have hCZ := (pair.mem_l M hZ hqZ).2
  obtain ⟨z₀, _, C₀, hCE, pair₀⟩ := (product q hqZ).mp hqD
  obtain ⟨ez, eC⟩ := (I).injective pair₀ pair
  subst z₀ C₀
  obtain ⟨b₀, _, col⟩ := (sequences C hCZ).mp hCE
  have eqb := col.domain_eq_l hZF.1 column
  subst b₀
  obtain ⟨e, codeω, edgeω⟩ := omega
  exact image C hCE col ⟨e, (col.bound_l edgeω).2, codeω, edgeω⟩ q hqD r (sub r hr) pair code hr

end YesMetaZFC.SetTheory.Internal
