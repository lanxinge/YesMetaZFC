import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Internal.TupleCode
import YesMetaZFC.Model.SetTheory.Types.SubtypeWitness
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Source.InaccessibleSyntax
import YesMetaZFC.Model.SetTheory.Embedding.Relative

/-! # 先于具体常量固定的内部查询程序

槽位表与程序只取决于内部元数和句子模板。实际名字列随后填入，
同一程序对每个合法名字列成立，因此可以连同列关系一起沿嵌入运输。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

structure Tt_packed_d (ω n : M.Domain) {k : Nat} (φ : Formula 1 (k+1)) (j : Fin k)
    (b : M.Domain) (σ : Fin k → M.Domain) (a z : M.Domain) : Prop where
  finite : M.mem n ω
  length : M.mem b ω
  natural : M.mem z ω
  prefix_bound : M.MemberSubset n b
  slots : ∀ i, M.mem (σ i) b
  cover : ∀ i, M.mem i b → M.mem i n ∨ ∃ j, i = σ j
  columns : ∀ U N, Tn_names_d n U N → ∀ v : Fin k → M.Domain, (∀ i, M.mem (v i) N) →
    ∃ C, M.IsSetFunctionFromTo Q C b N ∧ (∀ i, M.mem i n → Rd_entry_d i i C) ∧
      ∀ i, Rd_entry_d (σ i) (v i) C
  code : Sc_num_d Q ω a z
  compile : ∀ η Y c R f g (model : Smem_d Q c Y R)
      (ρ : Env (smdl_structure_l Q (R := R) model.1.2.1) k),
    V_d Q η Y → M.mem ω Y → M.IsSetFunctionFromTo Q f ω Y → M.IsSetFunctionFromTo K g ω Y →
    Sx_graph_d Q K f g → Rd_entry_d (σ j) ω f → (∀ i, Rd_entry_d (σ i) (ρ.bound i).val f) →
      (Satisfies_d Q ω c a f ↔ ∃ p : (smdl_structure_l Q (R := R) model.1.2.1).Domain,
        Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) φ)

theorem tt_packed_program_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    {k : Nat} (φ : Formula 1 (k+1)) (hc : φ.FreeClosed) (j : Fin k) :
    ∃ b σ a z, Tt_packed_d hZF ω n φ j b σ a z := by
  obtain ⟨b, σ, hb, nb, bounds, cover, columns⟩ := tt_column_build_l hZF hω hn k
  obtain ⟨a, m, G, u, form, compile⟩ := st_pack_bind_l hZF hω hb (bounds j) hn nb φ hc σ bounds
  obtain ⟨z, code⟩ := sc_num_exists_l Q hZF hω form
  exact ⟨b, σ, a, z, hn, hb, sc_num_natural_l Q hZF hω code, nb, bounds, cover, columns, code, compile⟩

theorem Tt_packed_d.query_l {ω n U N D b a z q C : M.Domain} (hω : M.IsOmega ω)
    {k : Nat} {φ : Formula 1 (k+1)} {j : Fin k} {σ : Fin k → M.Domain}
    (prog : Tt_packed_d hZF ω n φ j b σ a z) (pool : Tt_pool_d Q ω n U D) (names : Tn_names_d n U N)
    (v : Fin k → M.Domain) (column : M.IsSetFunctionFromTo Q C b N)
    (original : ∀ i, M.mem i n → Rd_entry_d i i C) (params : ∀ i, Rd_entry_d (σ i) (v i) C)
    (pair : (Q).Codes q z C) :
    M.mem q D ∧ ∀ η Y c R s δ t (model : Smem_d Q c Y R)
      (_type : Tt_realized_d Q ω c Y R n s δ U D t) (ρ : Env (smdl_structure_l Q (R := R) model.1.2.1) k),
      V_d Q η Y → (∀ i, Tn_value_d n s δ (v i) (ρ.bound i).val) → (ρ.bound j).val = ω →
        (M.mem q t ↔ ∃ g, M.IsSetFunctionFromTo K g ω Y ∧
          (∀ i x, M.mem i n → (Rd_entry_d i x s ↔ M.PairMember K i x g)) ∧
          ∃ p : (smdl_structure_l Q (R := R) model.1.2.1).Domain,
            Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) φ) := by
  obtain ⟨N', E, names', sequences, product⟩ := pool
  have eqN := hZF.1.eq_of_same_members N' N (fun x => (names' x).trans (names x).symm)
  subst N'
  have hz := prog.natural
  have hq := (product q).mpr ⟨z, hz, C, (sequences C).mpr ⟨b, prog.length, column⟩, pair⟩
  refine ⟨hq, fun η Y c R s δ t model type ρ hY values hw => ?_⟩
  have hωY : M.mem ω Y := hw ▸ (ρ.bound j).property
  obtain ⟨r, assign, fr⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) n prog.finite)
    type.tuple type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) column)
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l Q hZF (fn0_function_l (ZF.modelsKP hZF) fr) type.point
  have value i a x (ha : Rd_entry_d i a C) (hx : Tn_value_d n s δ a x) : Rd_entry_d i x f :=
    (fill.2 i x).mpr ⟨hω.transitive (ZF.modelsKP hZF) b prog.length i (column.input_mem_of_pairMember ha),
      Or.inl ⟨column.input_mem_of_pairMember ha, (assign.2 i x).mpr ⟨a, ha, hx⟩⟩⟩
  have vars i x (hx : Rd_entry_d i x s) : Rd_entry_d i x f :=
    value i i x (original i (type.tuple.bound_l hx).1) (Or.inl hx)
  have orig i x (hi : M.mem i n) : Rd_entry_d i x s ↔ Rd_entry_d i x f := by
    refine ⟨vars i x, fun hx => ?_⟩
    obtain ⟨y, _, hy⟩ := type.tuple.2.1 i hi
    exact ff.1.2 i y x (vars i y hy) hx ▸ hy
  obtain ⟨g, fg, agree⟩ := fn_recode_l Q K hZF ff
  have same i x hi := (orig i x hi).trans (agree i x).symm
  have read := (type.truth q).trans ((and_iff_right hq).trans
    ((tt_query_decode_l Q (ZF.modelsKP hZF) pair hz prog.length column.2.1 assign fill).trans
      ((sc_sat_decode_l Q hZF hω prog.code).trans
        (prog.compile η Y c R f g model ρ hY hωY ff fg agree
          (hw ▸ value (σ j) (v j) (ρ.bound j).val (params j) (values j))
          (fun i => value (σ i) (v i) (ρ.bound i).val (params i) (values i))))))
  refine read.trans ⟨fun ⟨p, cp, truth⟩ => ⟨g, fg, same, p, cp, truth⟩, ?_⟩
  rintro ⟨g', fg', same', p, cp, truth⟩
  have hωη := (v_ordinal_l Q hY).transitive ω (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal (ZF.modelsKP hZF)) hωY)
  obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hY hωη fg
  exact ⟨p, cp.transport_l K hZF hω fg' fg trace (fun i x hi => (same' i x hi).symm.trans (same i x hi)), truth⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型的同一固定查询与完整实现

程序码只依赖原元数；候选类型、较低域和元数都放在名字列中。
查询真值与任意内部元数、额外变量和排列的完整实现精确等价。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

def ts_template_m : Formula 1 8 :=
  ts_below_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest

theorem ts_template_closed_l : ts_template_m.FreeClosed :=
  ts_below_closed_l _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl

abbrev Ts_program_d (ω n b : M.Domain) (σ : Fin 7 → M.Domain) (a z : M.Domain) : Prop :=
  Tt_packed_d hZF ω n ts_template_m 6 b σ a z

theorem ts_program_l {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ b σ a z, Ts_program_d hZF ω n b σ a z :=
  tt_packed_program_l hZF hω hn ts_template_m ts_template_closed_l 6

theorem Ts_program_d.read_l {ω n U N D b a z q C : M.Domain} (hω : M.IsOmega ω)
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (pool : Tt_pool_d Q ω n U D) (names : Tn_names_d n U N)
    (v : Fin 7 → M.Domain) (column : M.IsSetFunctionFromTo Q C b N)
    (original : ∀ i, M.mem i n → Rd_entry_d i i C) (params : ∀ i, Rd_entry_d (σ i) (v i) C)
    (pair : (Q).Codes q z C) {η Y c R s δ t : M.Domain} (model : Smem_d Q c Y R)
    (type : Tt_realized_d Q ω c Y R n s δ U D t)
    (ρ : Env (smdl_structure_l Q (R := R) model.1.2.1) 7) (hY : V_d Q η Y)
    (values : ∀ i, Tn_value_d n s δ (v i) (ρ.bound i).val)
    (hw : (ρ.bound 6).val = ω) (hn : (ρ.bound 3).val = n) (hd : (ρ.bound 1).val = δ)
    {B V W : M.Domain} (hκ : M.IsLimitOrdinal (ρ.bound 5).val) (hτ : M.IsLimitOrdinal (ρ.bound 4).val)
    (hτκ : M.mem (ρ.bound 4).val (ρ.bound 5).val) (hm : M.mem (ρ.bound 2).val ω)
    (hB : V_d Q (ρ.bound 4).val B) (constants : ∀ x, M.mem x V ↔ M.mem x B ∨ x = (ρ.bound 4).val)
    (small : Tt_pool_d Q ω (ρ.bound 2).val V W) :
    M.mem q t ↔ M.MemberSubset n (ρ.bound 2).val ∧
      Ts_real_d hZF ω δ n s (ρ.bound 2).val V W (ρ.bound 0).val η := by
  have hωY : M.mem ω Y := hw ▸ (ρ.bound 6).property
  have hwV := (tt_constants_finite_l hZF hω hm hτ hB constants).1
  have atom (p : (smdl_structure_l Q (R := R) model.1.2.1).Domain) :
      Formula.satisfies (ρ.push p) ts_template_m ↔ M.MemberSubset n (ρ.bound 2).val ∧
        Ts_below_d hZF ω δ (ρ.bound 2).val V W (ρ.bound 0).val n p.val η := by
    let ε : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 8 := ⟨(ρ.push p).bound, (ρ.push p).free⟩
    have hw' : (.bound 7 : Term 8).eval ε = ⟨ω, hωY⟩ := Subtype.ext hw
    have read := ts_below_source_l hZF hω hY hωY ε (.bound 7) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest hw' hκ hτ hτκ hm hB constants small
    change Formula.satisfies ε ts_template_m ↔ M.MemberSubset (ρ.bound 3).val (ρ.bound 2).val ∧
      Ts_below_d hZF ω (ρ.bound 1).val (ρ.bound 2).val V W (ρ.bound 0).val (ρ.bound 3).val p.val η at read
    exact (smem_formula_l Q model _ ts_template_m ε).symm.trans (by simpa only [hn, hd] using read)
  have read := (prog.query_l hZF hω pool names v column original params pair).2
    η Y c R s δ t model type ρ hY values hw
  refine read.trans ⟨?_, ?_⟩
  · rintro ⟨g, fg, same, p, cp, truth⟩
    have ⟨nm, below⟩ := (atom p).mp truth
    exact ⟨nm, (ts_prefix_l hZF hω hY prog.finite hwV fg same).mp ⟨p.val, p.property, cp, below⟩⟩
  · rintro ⟨nm, real⟩
    obtain ⟨f, fill, ff⟩ := senv_fill_exists_l Q hZF (fn0_function_l (ZF.modelsKP hZF) type.tuple) type.point
    obtain ⟨g, fg, agree⟩ := fn_recode_l Q K hZF ff
    have same i x (hi : M.mem i n) : Rd_entry_d i x s ↔ M.PairMember K i x g := by
      have orig : Rd_entry_d i x s ↔ Rd_entry_d i x f := by
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · exact (fill.2 i x).mpr ⟨hω.transitive (ZF.modelsKP hZF) n prog.finite i hi, Or.inl ⟨hi, hx⟩⟩
        · exact ((fill.2 i x).mp hx).2.elim And.right (fun h => (h.1 hi).elim)
      exact orig.trans (agree i x).symm
    obtain ⟨p, hp, cp, below⟩ := (ts_prefix_l hZF hω hY prog.finite hwV fg same).mpr real
    exact ⟨g, fg, same, ⟨p, hp⟩, cp, (atom ⟨p, hp⟩).mpr ⟨nm, below⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 定义 3.6 的固定查询码

六个集合常量使用唯一的对角名字，指定常量使用原名字 n。
列的每个位置均由原变量或固定参数槽覆盖，故给定程序后查询码字面唯一。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_names_d (ω n κ τ m w : M.Domain) (v : Fin 7 → M.Domain) : Prop :=
  KPair_d M (v 0) w w ∧ v 1 = n ∧ KPair_d M (v 2) m m ∧ KPair_d M (v 3) n n ∧
    KPair_d M (v 4) τ τ ∧ KPair_d M (v 5) κ κ ∧ KPair_d M (v 6) ω ω

structure Ts_query_d (ω n κ τ m U w b : M.Domain) (σ : Fin 7 → M.Domain) (z q : M.Domain) : Prop where
  constants : M.mem w U ∧ M.mem m U ∧ M.mem n U ∧ M.mem τ U ∧ M.mem κ U ∧ M.mem ω U
  column : ∃ N C, ∃ v : Fin 7 → M.Domain, Tn_names_d n U N ∧ Fn0_d b N C ∧
    (∀ i, M.mem i n → Rd_entry_d i i C) ∧ (∀ i, Rd_entry_d (σ i) (v i) C) ∧
      Ts_names_d ω n κ τ m w v ∧ KPair_d M q z C

/-- 子类型只要求规定的查询属于 u，不要求 u 已有实现。 -/
def Ts_subtype_d (ω n κ τ m U w b : M.Domain) (σ : Fin 7 → M.Domain) (z u : M.Domain) : Prop :=
  M.mem τ κ ∧ M.MemberSubset n m ∧ ∃ q, Ts_query_d ω n κ τ m U w b σ z q ∧ M.mem q u

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ts_program_d.query_exists_l {ω n κ τ m U w D b a z : M.Domain}
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z) (pool : Tt_pool_d I ω n U D)
    (hc : M.mem w U ∧ M.mem m U ∧ M.mem n U ∧ M.mem τ U ∧ M.mem κ U ∧ M.mem ω U) :
    ∃ q, M.mem q D ∧ Ts_query_d ω n κ τ m U w b σ z q := by
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨v₀, h₀⟩ := (I).total w w
  obtain ⟨v₂, h₂⟩ := (I).total m m
  obtain ⟨v₃, h₃⟩ := (I).total n n
  obtain ⟨v₄, h₄⟩ := (I).total τ τ
  obtain ⟨v₅, h₅⟩ := (I).total κ κ
  obtain ⟨v₆, h₆⟩ := (I).total ω ω
  let v : Fin 7 → M.Domain := Fin.cases v₀ (Fin.cases n (Fin.cases v₂ (Fin.cases v₃
    (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆))))))
  have name x p (hx : M.mem x U) (hp : KPair_d M p x x) : M.mem p N :=
    (names p).mpr (Or.inr (Or.inr ⟨x, hx, hp⟩))
  have valid : ∀ i, M.mem (v i) N := Fin.cases (name w v₀ hc.1 h₀)
    (Fin.cases ((names n).mpr (Or.inr (Or.inl rfl))) (Fin.cases (name m v₂ hc.2.1 h₂)
      (Fin.cases (name n v₃ hc.2.2.1 h₃) (Fin.cases (name τ v₄ hc.2.2.2.1 h₄)
        (Fin.cases (name κ v₅ hc.2.2.2.2.1 h₅) (fun _ => name ω v₆ hc.2.2.2.2.2 h₆))))))
  obtain ⟨C, col, orig, params⟩ := prog.columns U N names v valid
  obtain ⟨q, pair⟩ := (I).total z C
  exact ⟨q, (prod q).mpr ⟨z, prog.natural, C, (seq C).mpr ⟨b, prog.length, col⟩, pair⟩,
    hc, N, C, v, names, fn0_of_function_l (ZF.modelsKP hZF) col, orig, params, ⟨h₀, rfl, h₂, h₃, h₄, h₅, h₆⟩, pair⟩

theorem Ts_query_d.unique_l {ω n κ τ m U w b a z q q' : M.Domain} {σ : Fin 7 → M.Domain}
    (prog : Ts_program_d hZF ω n b σ a z) (h : Ts_query_d ω n κ τ m U w b σ z q)
    (h' : Ts_query_d ω n κ τ m U w b σ z q') : q = q' := by
  obtain ⟨_, N, C, v, names, fc, orig, params, vals, pair⟩ := h
  obtain ⟨_, N', C', v', names', fc', orig', params', vals', pair'⟩ := h'
  have veq : v = v' := funext (Fin.cases (kpair_unique_l M hZF.1 vals.1 vals'.1)
    (Fin.cases (vals.2.1.trans vals'.2.1.symm) (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.1 vals'.2.2.1)
      (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.2.1 vals'.2.2.2.1)
        (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.2.2.1 vals'.2.2.2.2.1)
          (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.2.2.2.1 vals'.2.2.2.2.2.1)
            (Fin.cases (kpair_unique_l M hZF.1 vals.2.2.2.2.2.2 vals'.2.2.2.2.2.2) (fun i => Fin.elim0 i))))))))
  subst v'
  have carry {N C C' : M.Domain} (fn : Fn0_d b N C)
      (old : ∀ i, M.mem i n → Rd_entry_d i i C) (new : ∀ i, M.mem i n → Rd_entry_d i i C')
      (pa : ∀ i, Rd_entry_d (σ i) (v i) C) (pb : ∀ i, Rd_entry_d (σ i) (v i) C') i x
      (hx : Rd_entry_d i x C) : Rd_entry_d i x C' := by
    have f := fn0_function_l (ZF.modelsKP hZF) fn
    rcases prog.cover i (fn.bound_l hx).1 with hi | ⟨j, rfl⟩
    · exact (f.1.2 i x i hx (old i hi)).symm ▸ new i hi
    · exact (f.1.2 (σ j) x (v j) hx (pa j)).symm ▸ pb j
  have eqC := (fn0_function_l (ZF.modelsKP hZF) fc).1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) fc').1.1 (fun i x =>
      ⟨carry fc orig orig' params params' i x, carry fc' orig' orig params' params i x⟩)
  exact kpair_unique_l M hZF.1 pair (eqC.symm ▸ pair')

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型查询的自动构造与定义 3.7

候选低域类型的秩界自动保证其名字合法。固定程序及唯一查询码读取
原定义中的全部实现见证，允许任意内部有限元数和排列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ts_parameters_rank_l {ω κ τ n m B U A V D w : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hτκ : M.mem τ κ)
    (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hA : V_d I τ A) (small : ∀ x, M.mem x V ↔ M.mem x A ∨ x = τ)
    (pool : Tt_pool_d I ω m V D) (sub : M.MemberSubset w D) :
    M.mem w U ∧ M.mem m U ∧ M.mem n U ∧ M.mem τ U ∧ M.mem κ U ∧ M.mem ω U := by
  have hwκ := ordinal_down_l (ZF.modelsKP hZF) (hω.isOrdinal (ZF.modelsKP hZF)) hκ.1
    (hω.subset_limitOrdinal (ZF.modelsKP hZF) hτ) hτκ
  have hV := tt_constants_rank_l hZF hB hκ hτκ hA small
  have hD := pool.rank_mem_l (ZF.modelsKP hZF) hω hB hκ (ZF.v_ordinal_mem_l I hZF hB hwκ) hm hV
  have finite := tt_constants_finite_l hZF hω hn hκ hB constants
  exact ⟨(constants w).mpr (Or.inl (v_subset_mem_l I hB hD sub)),
    (tt_constants_finite_l hZF hω hm hκ hB constants).2, finite.2,
    (constants τ).mpr (Or.inl (ZF.v_ordinal_mem_l I hZF hB hτκ)),
    (constants κ).mpr (Or.inr rfl), finite.1⟩

theorem Ts_query_d.read_l {ω n κ τ m U w b a z q : M.Domain} (hω : M.IsOmega ω)
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z) (code : Ts_query_d ω n κ τ m U w b σ z q)
    {η Y c R s δ D t A V W : M.Domain} (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n s δ U D t)
    (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hτκ : M.mem τ κ) (hm : M.mem m ω)
    (hA : V_d I τ A) (constants : ∀ x, M.mem x V ↔ M.mem x A ∨ x = τ) (small : Tt_pool_d I ω m V W) :
    M.mem q t ↔ M.MemberSubset n m ∧ Ts_real_d hZF ω δ n s m V W w η := by
  obtain ⟨hc, N, C, v, names, col, orig, params, vals, pair⟩ := code
  let ρ : Env (smdl_structure_l I (R := R) model.1.2.1) 7 :=
    ⟨Fin.cases ⟨w, type.constants w hc.1⟩ (Fin.cases ⟨δ, type.point⟩
      (Fin.cases ⟨m, type.constants m hc.2.1⟩ (Fin.cases ⟨n, type.constants n hc.2.2.1⟩
        (Fin.cases ⟨τ, type.constants τ hc.2.2.2.1⟩ (Fin.cases ⟨κ, type.constants κ hc.2.2.2.2.1⟩
          (fun _ => ⟨ω, type.constants ω hc.2.2.2.2.2⟩)))))), fun _ => ⟨δ, type.point⟩⟩
  have values : ∀ i, Tn_value_d n s δ (v i) (ρ.bound i).val :=
    Fin.cases (Or.inr (Or.inr vals.1)) (Fin.cases (Or.inr (Or.inl ⟨vals.2.1, rfl⟩))
      (Fin.cases (Or.inr (Or.inr vals.2.2.1)) (Fin.cases (Or.inr (Or.inr vals.2.2.2.1))
        (Fin.cases (Or.inr (Or.inr vals.2.2.2.2.1)) (Fin.cases (Or.inr (Or.inr vals.2.2.2.2.2.1))
          (Fin.cases (Or.inr (Or.inr vals.2.2.2.2.2.2)) (fun i => Fin.elim0 i)))))))
  exact prog.read_l hZF hω type.pool names v (fn0_function_l (ZF.modelsKP hZF) col) orig params pair
    model type ρ hY values rfl rfl rfl hκ hτ hτκ hm hA constants small

theorem ts_subtype_realized_l {ω n κ τ m U w b a z : M.Domain} (hω : M.IsOmega ω)
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    {η Y c R s δ B D t A V W : M.Domain} (hY : V_d I η Y) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n s δ U D t)
    (hκ : M.IsLimitOrdinal κ) (hτ : M.IsLimitOrdinal τ) (hτκ : M.mem τ κ) (hm : M.mem m ω)
    (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hA : V_d I τ A) (small : ∀ x, M.mem x V ↔ M.mem x A ∨ x = τ)
    (pool : Tt_pool_d I ω m V W) (sub : M.MemberSubset w W) :
    Ts_subtype_d ω n κ τ m U w b σ z t ↔ M.MemberSubset n m ∧ Ts_real_d hZF ω δ n s m V W w η := by
  constructor
  · rintro ⟨_, _, q, code, hq⟩
    exact (code.read_l hZF hω prog hY model type hκ hτ hτκ hm hA small pool).mp hq
  · intro real
    obtain ⟨q, _, code⟩ := prog.query_exists_l hZF type.pool
      (ts_parameters_rank_l hZF hω prog.finite hm hκ hτ hτκ hB constants hA small pool sub)
    exact ⟨hτκ, real.1, q, code, (code.read_l hZF hω prog hY model type hκ hτ hτκ hm hA small pool).mpr real⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型程序编译性质的一阶矩阵

七个槽仅是固定模板的参数表；被打包的原变量数仍是任意内部自然数。
相对化展开定义原子后，矩阵与已有打包编译器的完整语义逐字等价。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

def ts_values_m {d} (Y p v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) : Formula 1 d :=
  sr_rel_m ts_template_m Y (Fin.cases p (Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂
    (Fin.cases v₃ (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆))))))))
@[simp] theorem ts_values_closed_l {d} (Y p v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d)
    (hY : Y.freeSupport = []) (hp : p.freeSupport = []) (h₀ : v₀.freeSupport = [])
    (h₁ : v₁.freeSupport = []) (h₂ : v₂.freeSupport = []) (h₃ : v₃.freeSupport = [])
    (h₄ : v₄.freeSupport = []) (h₅ : v₅.freeSupport = []) (h₆ : v₆.freeSupport = []) :
    (ts_values_m Y p v₀ v₁ v₂ v₃ v₄ v₅ v₆).FreeClosed :=
  sr_rel_closed_l ts_template_m ts_template_closed_l Y _ hY (Fin.cases hp (Fin.cases h₀
    (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅ (fun _ => h₆))))))))

def ts_compile_m {d} (ω n a : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪∀ η Y c R f g v₀ v₁ v₂ v₃ v₄ v₅ v₆,
  ⌜v_m kpair_convention_l⌝ₚ(η, Y) → ⌜ω⌝ₛ ∈ Y → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(f, ⌜ω⌝ₛ, Y) →
  ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(g, ⌜ω⌝ₛ, Y) →
  ⌜sx_graph_m (𝒞 := kpair_convention_l) (𝒟 := FlatPairing.convention)⌝ₚ(f, g) →
  ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, ⌜ω⌝ₛ, f) →
  ⌜rd_entry0_m⌝ₚ(⌜σ 0⌝ₛ, v₀, f) → ⌜rd_entry0_m⌝ₚ(⌜σ 1⌝ₛ, v₁, f) →
  ⌜rd_entry0_m⌝ₚ(⌜σ 2⌝ₛ, v₂, f) → ⌜rd_entry0_m⌝ₚ(⌜σ 3⌝ₛ, v₃, f) →
  ⌜rd_entry0_m⌝ₚ(⌜σ 4⌝ₛ, v₄, f) → ⌜rd_entry0_m⌝ₚ(⌜σ 5⌝ₛ, v₅, f) → ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, v₆, f) →
    (⌜satisfies_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c, ⌜a⌝ₛ, f) ↔ ∃ p ∈ Y,
      ⌜fs_code_m (𝒞 := FlatPairing.convention)⌝ₚ(⌜ω⌝ₛ, Y, g, ⌜n⌝ₛ, p) ∧
      ⌜ts_values_m⌝ₚ(Y, p, v₀, v₁, v₂, v₃, v₄, v₅, v₆))⟫

@[simp] theorem ts_compile_closed_l {d} (ω n a : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (ha : a.freeSupport = [])
    (hσ : ∀ j, (σ j).freeSupport = []) : (ts_compile_m ω n a σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_compile_m, Definitional.Formula.FreeClosed, hw, hn, ha, hσ]

def Ts_compile_d (ω n a : M.Domain) (σ : Fin 7 → M.Domain) : Prop :=
  ∀ η Y c R f g (model : Smem_d I c Y R) (ρ : Env (smdl_structure_l I (R := R) model.1.2.1) 7),
    V_d I η Y → M.mem ω Y → M.IsSetFunctionFromTo I f ω Y → M.IsSetFunctionFromTo K g ω Y →
    Sx_graph_d I K f g → Rd_entry_d (σ 6) ω f → (∀ j, Rd_entry_d (σ j) (ρ.bound j).val f) →
      (Satisfies_d I ω c a f ↔ ∃ p : (smdl_structure_l I (R := R) model.1.2.1).Domain,
        Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) ts_template_m)

private theorem ts_values_sat_l {Y : M.Domain} (ny : Nonempty {x // M.mem x Y}) {d}
    (θ : Env M d) (T p v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) (ρ : Env (rt_model_l Y ny) 7)
    (x : (rt_model_l Y ny).Domain) (hY : T.eval θ = Y) (hp : p.eval θ = x.val)
    (hv : ∀ j, ((Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂ (Fin.cases v₃
      (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆)))))) : Fin 7 → Term d) j).eval θ = (ρ.bound j).val) :
    Formula.satisfies θ (ts_values_m T p v₀ v₁ v₂ v₃ v₄ v₅ v₆) ↔ Formula.satisfies (ρ.push x) ts_template_m :=
  sr_rel_sat_l ny ts_template_m ts_template_closed_l (ρ.push x) θ T _ hY (Fin.cases hp hv)

theorem ts_compile_sat_l {d} (θ : Env M d) (ω n a : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies θ (ts_compile_m ω n a σ) ↔
      Ts_compile_d hZF (ω.eval θ) (n.eval θ) (a.eval θ) (fun j => (σ j).eval θ) := by
  simp only [ts_compile_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    v_sat_l I hZF.1, Formula.satisfies_mem_iff, smem_sat_l I,
    Formula.satisfies_isFunctionFromTo_iff I hZF.1, Formula.satisfies_isFunctionFromTo_iff K hZF.1,
    sx_graph_sat_l I K, rd_entry0_sat_l hZF.1, Formula.satisfies_iff_iff, satisfies_sat_l I hZF.1,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, fs_code_sat_l K hZF.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · intro h η Y c R f g model ρ hY hw ff fg same fw values
    have read := h η Y c R f g (ρ.bound 0).val (ρ.bound 1).val (ρ.bound 2).val (ρ.bound 3).val
      (ρ.bound 4).val (ρ.bound 5).val (ρ.bound 6).val hY hw model ff fg same fw
      (values 0) (values 1) (values 2) (values 3) (values 4) (values 5) (values 6)
    refine read.trans ?_
    let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω.eval θ, hw⟩⟩
    let ρ' : Env (rt_model_l Y ny) 7 := ⟨ρ.bound, ρ.free⟩
    let ξ (p : M.Domain) := (((((((((((((θ.push η).push Y).push c).push R).push f).push g).push (ρ.bound 0).val).push
      (ρ.bound 1).val).push (ρ.bound 2).val).push (ρ.bound 3).val).push (ρ.bound 4).val).push (ρ.bound 5).val).push (ρ.bound 6).val).push p
    have atom (p : (rt_model_l Y ny).Domain) :=
      (ts_values_sat_l ny (ξ p.val) (.bound 12) .newest (.bound 7) (.bound 6) (.bound 5) (.bound 4)
        (.bound 3) (.bound 2) (.bound 1) ρ' p rfl rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))).trans
        (smem_formula_l I model ny ts_template_m (ρ'.push p))
    exact ⟨fun ⟨p, hp, cp, truth⟩ => ⟨⟨p, hp⟩, cp, (atom ⟨p, hp⟩).mp truth⟩,
      fun ⟨p, cp, truth⟩ => ⟨p.val, p.property, cp, (atom p).mpr truth⟩⟩
  · intro h η Y c R f g v₀ v₁ v₂ v₃ v₄ v₅ v₆ hY hw model ff fg same fw h₀ h₁ h₂ h₃ h₄ h₅ h₆
    let v : Fin 7 → M.Domain := Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂ (Fin.cases v₃
      (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆))))))
    have values : ∀ j, Rd_entry_d ((σ j).eval θ) (v j) f := Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂
      (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅ (Fin.cases h₆ (fun j => Fin.elim0 j)))))))
    let ρ : Env (smdl_structure_l I (R := R) model.1.2.1) 7 :=
      ⟨fun j => ⟨v j, ff.output_mem_of_pairMember (values j)⟩, fun _ => ⟨ω.eval θ, hw⟩⟩
    refine (h η Y c R f g model ρ hY hw ff fg same fw values).trans ?_
    let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω.eval θ, hw⟩⟩
    let ρ' : Env (rt_model_l Y ny) 7 := ⟨ρ.bound, ρ.free⟩
    let ξ (p : M.Domain) := (((((((((((((θ.push η).push Y).push c).push R).push f).push g).push v₀).push v₁).push v₂).push v₃).push v₄).push v₅).push v₆).push p
    have atom (p : (rt_model_l Y ny).Domain) :=
      (ts_values_sat_l ny (ξ p.val) (.bound 12) .newest (.bound 7) (.bound 6) (.bound 5) (.bound 4)
        (.bound 3) (.bound 2) (.bound 1) ρ' p rfl rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))).trans
        (smem_formula_l I model ny ts_template_m (ρ'.push p))
    exact ⟨fun ⟨p, cp, truth⟩ => ⟨p.val, p.property, cp, (atom p).mpr truth⟩,
      fun ⟨p, hp, cp, truth⟩ => ⟨⟨p, hp⟩, cp, (atom ⟨p, hp⟩).mp truth⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型程序与固定槽位表的原公式

编译矩阵之外，原变量前缀、全部参数槽覆盖和实际名字列构造也写入证书。
因此从内部表取出的程序直接满足原 `Ts_program_d`，无须补交列生成器。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_eval_cases_l {d k} (ρ : Env M d) (a : Term d) (b : Fin k → Term d) :
    (fun j : Fin (k + 1) => (Fin.cases a b j : Term d).eval ρ) =
      (fun j => Fin.cases (a.eval ρ) (fun j => (b j).eval ρ) j) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

def ts_columns_m {d} (n b : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪∀ U N v₀ v₁ v₂ v₃ v₄ v₅ v₆,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, U, N) → v₀ ∈ N → v₁ ∈ N → v₂ ∈ N → v₃ ∈ N → v₄ ∈ N → v₅ ∈ N → v₆ ∈ N →
    ∃ C, ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(C, ⌜b⌝ₛ, N) ∧
    (∀ i ∈ ⌜n⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, C)) ∧
    ⌜rd_entry0_m⌝ₚ(⌜σ 0⌝ₛ, v₀, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 1⌝ₛ, v₁, C) ∧
    ⌜rd_entry0_m⌝ₚ(⌜σ 2⌝ₛ, v₂, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 3⌝ₛ, v₃, C) ∧
    ⌜rd_entry0_m⌝ₚ(⌜σ 4⌝ₛ, v₄, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 5⌝ₛ, v₅, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, v₆, C)⟫

@[simp] theorem ts_columns_closed_l {d} (n b : Term d) (σ : Fin 7 → Term d)
    (hn : n.freeSupport = []) (hb : b.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (ts_columns_m n b σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_columns_m, Definitional.Formula.FreeClosed, hn, hb, hσ]

theorem ts_columns_sat_l {d} (ρ : Env M d) (n b : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_columns_m n b σ) ↔
      ∀ U N, Tn_names_d (n.eval ρ) U N → ∀ v : Fin 7 → M.Domain, (∀ j, M.mem (v j) N) →
        ∃ C, M.IsSetFunctionFromTo I C (b.eval ρ) N ∧
          (∀ j, M.mem j (n.eval ρ) → Rd_entry_d j j C) ∧ ∀ j, Rd_entry_d ((σ j).eval ρ) (v j) C := by
  simp only [ts_columns_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    tn_names0_sat_l (ZF.modelsKP hZF), Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_isFunctionFromTo_iff I hZF.1,
    rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · intro h U N names v valid
    obtain ⟨C, fn, old, h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h U N (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
      names (valid 0) (valid 1) (valid 2) (valid 3) (valid 4) (valid 5) (valid 6)
    exact ⟨C, fn, old, Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄
      (Fin.cases h₅ (Fin.cases h₆ (fun j => Fin.elim0 j)))))))⟩
  · intro h U N v₀ v₁ v₂ v₃ v₄ v₅ v₆ names h₀ h₁ h₂ h₃ h₄ h₅ h₆
    obtain ⟨C, fn, old, values⟩ := h U N names (Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂
      (Fin.cases v₃ (Fin.cases v₄ (Fin.cases v₅ (fun _ => v₆)))))))
      (Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅ (fun _ => h₆)))))))
    exact ⟨C, fn, old, values 0, values 1, values 2, values 3, values 4, values 5, values 6⟩

def ts_program0_m : Formula 1 12 :=
  let p : Fin 12 → Term 12 := Term.bound
  let σ : Fin 7 → Term 12 := fun i => [p 5, p 6, p 7, p 8, p 9, p 10, p 11].get i
  set[12] ⟪⌜p 1⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 2⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 4⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 1⌝ₛ ⊆ ⌜p 2⌝ₛ ∧
    ⌜p 5⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 6⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 7⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 8⌝ₛ ∈ ⌜p 2⌝ₛ ∧
    ⌜p 9⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 10⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜p 11⌝ₛ ∈ ⌜p 2⌝ₛ ∧
    (∀ j ∈ ⌜p 2⌝ₛ, j ∈ ⌜p 1⌝ₛ ∨ j = ⌜p 5⌝ₛ ∨ j = ⌜p 6⌝ₛ ∨ j = ⌜p 7⌝ₛ ∨ j = ⌜p 8⌝ₛ ∨
      j = ⌜p 9⌝ₛ ∨ j = ⌜p 10⌝ₛ ∨ j = ⌜p 11⌝ₛ) ∧
    ⌜ts_columns_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜σ⌝ₛ) ∧ ⌜sc_num_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 0⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ) ∧
    ⌜ts_compile_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜σ⌝ₛ)⟫

theorem ts_program0_closed_l : ts_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [ts_program0_m, Definitional.Formula.FreeClosed]
  have hs : ∀ i : Fin 7, ([Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8,
      Term.bound 9, Term.bound 10, Term.bound 11].get i : Term 12).freeSupport = [] := by
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  exact ⟨ts_columns_closed_l _ _ _ rfl rfl hs, ts_compile_closed_l _ _ _ _ rfl rfl rfl hs⟩

def ts_program_m {d} (ω n b a z : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  ts_program0_m.bind (fun i => [ω, n, b, a, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)

@[simp] theorem ts_program_closed_l {d} (ω n b a z : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hb : b.freeSupport = [])
    (ha : a.freeSupport = []) (hz : z.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (ts_program_m ω n b a z σ).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ts_program0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hn, hb, ha, hz, hσ 0, hσ 1, hσ 2, hσ 3, hσ 4, hσ 5, hσ 6, fun i => Fin.elim0 i⟩

theorem ts_program_sat_l {d} (ρ : Env M d) (ω n b a z : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_program_m ω n b a z σ) ↔
      Ts_program_d hZF (ω.eval ρ) (n.eval ρ) (b.eval ρ) (fun j => (σ j).eval ρ) (a.eval ρ) (z.eval ρ) := by
  have eta (j : Fin 7) :
      ([Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8, Term.bound 9, Term.bound 10, Term.bound 11].get j : Term 12).eval
        (Definitional.Env.substitute ρ (fun i => [ω, n, b, a, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)) =
      (σ j).eval ρ := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))) j
  simp only [ts_program_m, Formula.satisfies_bind, ts_program0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    ts_columns_sat_l hZF, sc_num_sat_l I hZF.1, ts_compile_sat_l hZF,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, eta]
  constructor
  · rintro ⟨hn, hb, hz, nb, h₀, h₁, h₂, h₃, h₄, h₅, h₆, cover, columns, code, compile⟩
    refine ⟨hn, hb, hz, nb, Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄
      (Fin.cases h₅ (Fin.cases h₆ (fun j => Fin.elim0 j))))))), ?_, columns, code, compile⟩
    intro j hj
    simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false]
    exact cover j hj
  · intro p
    refine ⟨p.finite, p.length, p.natural, p.prefix_bound, p.slots 0, p.slots 1, p.slots 2, p.slots 3,
      p.slots 4, p.slots 5, p.slots 6, ?_, p.columns, p.code, p.compile⟩
    intro j hj
    have h := p.cover j hj
    simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at h
    exact h

/-- 程序文本由原自然数码约束；向外只暴露 ω 及十个自然数参数。 -/
def ts_numeric0_m : Formula 1 11 := .existsE (ts_program_m
  (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4)
  (fun i => [Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8, Term.bound 9, Term.bound 10, Term.bound 11].get i))

theorem ts_numeric0_closed_l : ts_numeric0_m.FreeClosed := by
  simp -implicitDefEqProofs [ts_numeric0_m, Definitional.Formula.FreeClosed]
  apply ts_program_closed_l <;> try rfl
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i

theorem ts_numeric0_sat_l (ρ : Env M 11) : Formula.satisfies ρ ts_numeric0_m ↔
    ∃ a, Ts_program_d hZF (ρ.bound 0) (ρ.bound 1) (ρ.bound 2)
      (fun i => [ρ.bound 4, ρ.bound 5, ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10].get i) a (ρ.bound 3) := by
  simp only [ts_numeric0_m, Formula.satisfies_exists_iff, ts_program_sat_l hZF]
  refine exists_congr fun a => ?_
  have eq : (fun i : Fin 7 =>
      ([Term.bound 5, Term.bound 6, Term.bound 7, Term.bound 8, Term.bound 9, Term.bound 10, Term.bound 11].get i : Term 12).eval (ρ.push a)) =
      (fun i => [ρ.bound 4, ρ.bound 5, ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10].get i) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  rw [eq]
  rfl

def ts_numeric_m {d} (ω n b z : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  ts_numeric0_m.bind (fun i => [ω, n, b, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)

@[simp] theorem ts_numeric_closed_l {d} (ω n b z : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hb : b.freeSupport = []) (hz : z.freeSupport = [])
    (hσ : ∀ i, (σ i).freeSupport = []) : (ts_numeric_m ω n b z σ).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr ts_numeric0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hn, hb, hz, hσ 0, hσ 1, hσ 2, hσ 3, hσ 4, hσ 5, hσ 6, fun i => Fin.elim0 i⟩

theorem ts_numeric_sat_l {d} (ρ : Env M d) (ω n b z : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_numeric_m ω n b z σ) ↔
      ∃ a, Ts_program_d hZF (ω.eval ρ) (n.eval ρ) (b.eval ρ) (fun i => (σ i).eval ρ) a (z.eval ρ) := by
  simp only [ts_numeric_m, Formula.satisfies_bind, ts_numeric0_sat_l hZF]
  have eq : (fun i : Fin 7 => [(σ 0).eval ρ, (σ 1).eval ρ, (σ 2).eval ρ, (σ 3).eval ρ,
      (σ 4).eval ρ, (σ 5).eval ρ, (σ 6).eval ρ].get i) = (fun i => (σ i).eval ρ) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  exact exists_congr fun a => by rw [← eq]; rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型程序经共同根传递

把实际程序文本存在绑定后，留下的元数、长度、代码及七个槽位全是自然数。
两条完整初等图固定这些参数，所以目标取得同一码所约束的完整编译证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_program_in_d (ω n b z : M.Domain) (σ : Fin 7 → M.Domain) (C : M.Domain) : Prop :=
  let p : Fin 11 → M.Domain := fun i => [ω, n, b, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  (∀ i, M.mem (p i) C) ∧ Formula.satisfies ((⟨p, fun _ => ω⟩ : Env M 11).push C)
    (lr_rel_m ts_numeric0_m .newest (fun i => .bound i.succ))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω r B R w z x X S y Y T π σ C₀ C D : M.Domain}
  (nc : Nonempty {a // M.mem a C}) (ρ : Env (rt_model_l C nc) 12)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem ts_program_peer_l (hω : M.IsOmega ω)
    (numbers : Rr_layer_d I ω B R w z) (rootExt : Rf_ext_d I B R)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mb : Smdl_d I r B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω r x B X π) (k : Smap_d I ω r y B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (ct : M.TransitiveSet C) (dt : M.TransitiveSet D) (hwD : M.mem ω D)
    (hw : p 0 = ω) (valid : Formula.satisfies ρ ts_program0_m) :
    Ts_program_in_d ω (p 1) (p 2) (p 4) (fun i => [p 5, p 6, p 7, p 8, p 9, p 10, p 11].get i) D := by
  have data := valid
  simp only [ts_program0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at data
  obtain ⟨hn, hb, hz, _, h₀, h₁, h₂, h₃, h₄, h₅, h₆, _⟩ := data
  have hwC : M.mem ω C := hw ▸ (ρ.bound 0).property
  let q : Fin 11 → M.Domain := fun i => [ω, p 1, p 2, p 4, p 5, p 6, p 7, p 8, p 9, p 10, p 11].get i
  have small a (ha : M.mem a (p 2)) := hω.transitive (ZF.modelsKP hZF) (p 2) (hw ▸ hb) a ha
  have low : ∀ i, q i = ω ∨ M.mem (q i) ω := by
    simp only [Fin.forall_fin_succ]
    exact ⟨Or.inl rfl, Or.inr (hw ▸ hn), Or.inr (hw ▸ hb), Or.inr (hw ▸ hz),
      Or.inr (small _ h₀), Or.inr (small _ h₁), Or.inr (small _ h₂), Or.inr (small _ h₃),
      Or.inr (small _ h₄), Or.inr (small _ h₅), Or.inr (small _ h₆), fun i => Fin.elim0 i⟩
  have inC i : M.mem (q i) C := (low i).elim (fun eq => eq.symm ▸ hwC) (ct ω hwC _)
  have inD i : M.mem (q i) D := (low i).elim (fun eq => eq.symm ▸ hwD) (dt ω hwD _)
  let ξ : Env (rt_model_l C nc) 11 := ⟨fun i => ⟨q i, inC i⟩, fun _ => ⟨ω, hwC⟩⟩
  let nd : Nonempty {a // M.mem a D} := ⟨⟨ω, hwD⟩⟩
  let θ : Env (rt_model_l D nd) 11 := ⟨fun i => ⟨q i, inD i⟩, fun _ => ⟨ω, hwD⟩⟩
  have code : Formula.satisfies ξ ts_numeric0_m := by
    simp only [ts_numeric0_m, Formula.satisfies_exists_iff, ts_program_m, Formula.satisfies_bind]
    refine ⟨ρ.bound 3, (Formula.closed_env_l ts_program0_m ts_program0_closed_l ?_).mp valid⟩
    funext i
    exact Fin.cases (Subtype.ext hw) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
  have moved := (smap_numeric_peer_l hZF hω numbers rootExt xt yt mb mx my j k iC iD ct dt nc nd
    ts_numeric0_m ts_numeric0_closed_l ξ θ (fun _ => rfl) low).mp code
  exact ⟨inD, (sc_relative_sat_l dt nd ts_numeric0_m ts_numeric0_closed_l θ
    ((⟨q, fun _ => ω⟩ : Env M 11).push D) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).mpr moved⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 裸类型中固定子类型查询的原公式

量化的名字列仍保留原前缀，并在既定程序槽位填入六个对角常量及指定点。
本文件只展开实际查询的编码，不用语义等价替换类型中的字面成员条件。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def ts_names_m {d} (ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) : Formula 1 d := set[d] ⟪
  ⌜kpair0_m⌝ₚ(⌜v₀⌝ₛ, ⌜w⌝ₛ, ⌜w⌝ₛ) ∧ ⌜v₁⌝ₛ = ⌜n⌝ₛ ∧ ⌜kpair0_m⌝ₚ(⌜v₂⌝ₛ, ⌜m⌝ₛ, ⌜m⌝ₛ) ∧
  ⌜kpair0_m⌝ₚ(⌜v₃⌝ₛ, ⌜n⌝ₛ, ⌜n⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(⌜v₄⌝ₛ, ⌜τ⌝ₛ, ⌜τ⌝ₛ) ∧
  ⌜kpair0_m⌝ₚ(⌜v₅⌝ₛ, ⌜κ⌝ₛ, ⌜κ⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(⌜v₆⌝ₛ, ⌜ω⌝ₛ, ⌜ω⌝ₛ)⟫
derive_free_closed ts_names_m

theorem ts_names_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) :
    Formula.satisfies ρ (ts_names_m ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆) ↔
      Ts_names_d (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (m.eval ρ) (w.eval ρ)
        (Fin.cases (v₀.eval ρ) (Fin.cases (v₁.eval ρ) (Fin.cases (v₂.eval ρ) (Fin.cases (v₃.eval ρ)
          (Fin.cases (v₄.eval ρ) (Fin.cases (v₅.eval ρ) (fun _ => v₆.eval ρ))))))) := by
  simp only [ts_names_m, Ts_names_d, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, kpair0_sat_l hE]
  rfl

def ts_query_m {d} (ω n κ τ m U w b z q : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪
  (⌜w⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜m⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜n⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜τ⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜U⌝ₛ ∧ ⌜ω⌝ₛ ∈ ⌜U⌝ₛ) ∧
  (∃ N C v₀ v₁ v₂ v₃ v₄ v₅ v₆, ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜fn0_m⌝ₚ(⌜b⌝ₛ, N, C) ∧
    (∀ i ∈ ⌜n⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, C)) ∧
    (⌜rd_entry0_m⌝ₚ(⌜σ 0⌝ₛ, v₀, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 1⌝ₛ, v₁, C) ∧
      ⌜rd_entry0_m⌝ₚ(⌜σ 2⌝ₛ, v₂, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 3⌝ₛ, v₃, C) ∧
      ⌜rd_entry0_m⌝ₚ(⌜σ 4⌝ₛ, v₄, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 5⌝ₛ, v₅, C) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, v₆, C)) ∧
    ⌜ts_names_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜κ⌝ₛ, ⌜τ⌝ₛ, ⌜m⌝ₛ, ⌜w⌝ₛ, v₀, v₁, v₂, v₃, v₄, v₅, v₆) ∧
    ⌜kpair0_m⌝ₚ(⌜q⌝ₛ, ⌜z⌝ₛ, C))⟫

@[simp] theorem ts_query_closed_l {d} (ω n κ τ m U w b z q : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hk : κ.freeSupport = []) (ht : τ.freeSupport = [])
    (hm : m.freeSupport = []) (hU : U.freeSupport = []) (hW : w.freeSupport = []) (hb : b.freeSupport = [])
    (hz : z.freeSupport = []) (hq : q.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (ts_query_m ω n κ τ m U w b z q σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_query_m, Definitional.Formula.FreeClosed, hw, hn, hk, ht, hm, hU, hW, hb, hz, hq, hσ]

theorem ts_query_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω n κ τ m U w b z q : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_query_m ω n κ τ m U w b z q σ) ↔ Ts_query_d
      (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (m.eval ρ) (U.eval ρ) (w.eval ρ) (b.eval ρ)
      (fun j => (σ j).eval ρ) (z.eval ρ) (q.eval ρ) := by
  simp only [ts_query_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, tn_names0_sat_l hKP, fn0_sat_l hKP.1, rd_entry0_sat_l hKP.1,
    ts_names_sat_l hKP.1, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨constants, N, C, v₀, v₁, v₂, v₃, v₄, v₅, v₆, names, fn, old, slots, values, pair⟩
    obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := slots
    exact ⟨constants, N, C, _, names, fn, old,
      Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄
        (Fin.cases h₅ (Fin.cases h₆ (fun j => Fin.elim0 j))))))), values, pair⟩
  · rintro ⟨constants, N, C, v, names, fn, old, slots, values, pair⟩
    refine ⟨constants, N, C, v 0, v 1, v 2, v 3, v 4, v 5, v 6, names, fn, old,
      ⟨slots 0, slots 1, slots 2, slots 3, slots 4, slots 5, slots 6⟩, ?_, pair⟩
    exact values

def ts_subtype_m {d} (ω n κ τ m U w b z u : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  .conj (.mem τ κ) (.conj (Formula.subset n m) (.existsE (.conj
    (ts_query_m ω.weaken n.weaken κ.weaken τ.weaken m.weaken U.weaken w.weaken b.weaken z.weaken .newest
      (fun j => (σ j).weaken)) (.mem .newest u.weaken))))

@[simp] theorem ts_subtype_closed_l {d} (ω n κ τ m U w b z u : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hk : κ.freeSupport = []) (ht : τ.freeSupport = [])
    (hm : m.freeSupport = []) (hU : U.freeSupport = []) (hW : w.freeSupport = []) (hb : b.freeSupport = [])
    (hz : z.freeSupport = []) (hu : u.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (ts_subtype_m ω n κ τ m U w b z u σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_subtype_m, Definitional.Formula.FreeClosed, hw, hn, hk, ht, hm, hU, hW, hb, hz, hu, hσ]

theorem ts_subtype_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω n κ τ m U w b z u : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_subtype_m ω n κ τ m U w b z u σ) ↔ Ts_subtype_d
      (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (m.eval ρ) (U.eval ρ) (w.eval ρ) (b.eval ρ)
      (fun j => (σ j).eval ρ) (z.eval ρ) (u.eval ρ) := by
  simp only [ts_subtype_m, Ts_subtype_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_exists_iff, ts_query_sat_l hKP, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型名字列的有界原式

所有七个名字均在给定名字域中量化，原变量列与固定槽位保持不变。
这使定义域参数的统一替换能够覆盖超幂中没有原像的新名字列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Ts_column_d (ω n κ τ m N w b : M.Domain) (σ : Fin 7 → M.Domain) (C : M.Domain) : Prop :=
  Fn0_d b N C ∧ (∀ i, M.mem i n → Rd_entry_d i i C) ∧ ∃ v : Fin 7 → M.Domain,
    (∀ i, M.mem (v i) N) ∧ (∀ i, Rd_entry_d (σ i) (v i) C) ∧ Ts_names_d ω n κ τ m w v

def ts_column_m {d} (ω n κ τ m N w b C : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜b⌝ₛ, ⌜N⌝ₛ, ⌜C⌝ₛ) ∧ (∀ i ∈ ⌜n⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, ⌜C⌝ₛ)) ∧
  (∃ v₀ ∈ ⌜N⌝ₛ, ∃ v₁ ∈ ⌜N⌝ₛ, ∃ v₂ ∈ ⌜N⌝ₛ, ∃ v₃ ∈ ⌜N⌝ₛ, ∃ v₄ ∈ ⌜N⌝ₛ, ∃ v₅ ∈ ⌜N⌝ₛ, ∃ v₆ ∈ ⌜N⌝ₛ,
    (⌜rd_entry0_m⌝ₚ(⌜σ 0⌝ₛ, v₀, ⌜C⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 1⌝ₛ, v₁, ⌜C⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜σ 2⌝ₛ, v₂, ⌜C⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 3⌝ₛ, v₃, ⌜C⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜σ 4⌝ₛ, v₄, ⌜C⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 5⌝ₛ, v₅, ⌜C⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜σ 6⌝ₛ, v₆, ⌜C⌝ₛ)) ∧
    ⌜ts_names_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜κ⌝ₛ, ⌜τ⌝ₛ, ⌜m⌝ₛ, ⌜w⌝ₛ, v₀, v₁, v₂, v₃, v₄, v₅, v₆))⟫

@[simp] theorem ts_column_closed_l {d} (ω n κ τ m N w b C : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hk : κ.freeSupport = []) (ht : τ.freeSupport = [])
    (hm : m.freeSupport = []) (hN : N.freeSupport = []) (hu : w.freeSupport = []) (hb : b.freeSupport = [])
    (hC : C.freeSupport = []) (hσ : ∀ i, (σ i).freeSupport = []) : (ts_column_m ω n κ τ m N w b C σ).FreeClosed := by
  simp -implicitDefEqProofs [ts_column_m, Definitional.Formula.FreeClosed, hw, hn, hk, ht, hm, hN, hu, hb, hC, hσ]

theorem ts_names_delta_l {d} (ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆ : Term d) :
    (ts_names_m ω n κ τ m w v₀ v₁ v₂ v₃ v₄ v₅ v₆).IsDelta0 :=
  .conj (kpair0_delta_l ..) (.conj (.atom ..) (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..)
    (.conj (kpair0_delta_l ..) (.conj (kpair0_delta_l ..) (kpair0_delta_l ..))))))

theorem ts_column_delta_l {d} (ω n κ τ m N w b C : Term d) (σ : Fin 7 → Term d) :
    (ts_column_m ω n κ τ m N w b C σ).IsDelta0 :=
  .conj (fn0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..))
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
        (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))))
        (ts_names_delta_l ..))))))))))

theorem ts_column_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (ω n κ τ m N w b C : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (ts_column_m ω n κ τ m N w b C σ) ↔ Ts_column_d
      (ω.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (m.eval ρ) (N.eval ρ) (w.eval ρ) (b.eval ρ)
      (fun i => (σ i).eval ρ) (C.eval ρ) := by
  simp only [ts_column_m, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, rd_entry0_sat_l hE, ts_names_sat_l hE, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨fn, orig, v₀, h₀, v₁, h₁, v₂, h₂, v₃, h₃, v₄, h₄, v₅, h₅, v₆, h₆, ⟨s₀, s₁, s₂, s₃, s₄, s₅, s₆⟩, vals⟩
    exact ⟨fn, orig, _, Fin.cases h₀ (Fin.cases h₁ (Fin.cases h₂ (Fin.cases h₃ (Fin.cases h₄ (Fin.cases h₅
      (Fin.cases h₆ (fun j => Fin.elim0 j))))))), Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃
      (Fin.cases s₄ (Fin.cases s₅ (Fin.cases s₆ (fun j => Fin.elim0 j))))))), vals⟩
  · rintro ⟨fn, orig, v, mem, slots, vals⟩
    exact ⟨fn, orig, v 0, mem 0, v 1, mem 1, v 2, mem 2, v 3, mem 3, v 4, mem 4, v 5, mem 5, v 6, mem 6,
      ⟨slots 0, slots 1, slots 2, slots 3, slots 4, slots 5, slots 6⟩, vals⟩

theorem Ts_column_d.query_l {ω n κ τ m U N w b z q C : M.Domain} {σ : Fin 7 → M.Domain}
    (h : Ts_column_d ω n κ τ m N w b σ C) (names : Tn_names_d n U N)
    (constants : M.mem w U ∧ M.mem m U ∧ M.mem n U ∧ M.mem τ U ∧ M.mem κ U ∧ M.mem ω U)
    (code : KPair_d M q z C) : Ts_query_d ω n κ τ m U w b σ z q := by
  obtain ⟨fn, orig, v, _, slots, vals⟩ := h
  exact ⟨constants, N, C, v, names, fn, orig, slots, vals, code⟩

theorem Ts_query_d.column_l (hE : Extensional M) {ω n κ τ m U N w b z q : M.Domain}
    {σ : Fin 7 → M.Domain} (h : Ts_query_d ω n κ τ m U w b σ z q) (names : Tn_names_d n U N) :
    ∃ C, Ts_column_d ω n κ τ m N w b σ C ∧ KPair_d M q z C := by
  obtain ⟨_, N', C, v, names', fn, orig, slots, vals, code⟩ := h
  have eq := hE.eq_of_same_members N' N (fun x => (names' x).trans (names x).symm)
  subst N'
  exact ⟨C, ⟨fn, orig, v, fun i => (fn.bound_l (slots i)).2, slots, vals⟩, code⟩

/-- 原查询属于新查询域时，它的六个实际常量自动属于新常量域。 -/
theorem Ts_query_d.pool_l (hKP : M.Models KP) {ω n κ τ m U V D w b z q : M.Domain} {σ : Fin 7 → M.Domain}
    (h : Ts_query_d ω n κ τ m U w b σ z q) (on : M.IsOrdinal n)
    (pool : Tt_pool_d (kp_pair_l hKP) ω n V D) (hq : M.mem q D) : Ts_query_d ω n κ τ m V w b σ z q := by
  obtain ⟨_, N₀, C, v, _, fn, orig, slots, vals, code⟩ := h
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨z', _, C', hC, code'⟩ := (prod q).mp hq
  obtain ⟨hz, hc⟩ := kpair_injective_l M code' code
  subst z' C'
  obtain ⟨b', _, fn'⟩ := (seq C).mp hC
  have eq := (fn0_of_function_l hKP fn').domain_eq_l hKP.1 fn
  subst b'
  have value i x (cp : KPair_d M (v i) x x) : M.mem x V := by
    rcases (names (v i)).mp (fn'.output_mem_of_pairMember (slots i)) with hi | eq | ⟨y, hy, cy⟩
    · exact (cp.not_transitive_l M (KP.mem_irrefl_d hKP) (on.mem hi).transitive).elim
    · exact (cp.not_transitive_l M (KP.mem_irrefl_d hKP) (eq.symm ▸ on.transitive)).elim
    · exact (kpair_injective_l M cy cp).1 ▸ hy
  exact ⟨⟨value 0 w vals.1, value 2 m vals.2.2.1, value 3 n vals.2.2.2.1,
      value 4 τ vals.2.2.2.2.1, value 5 κ vals.2.2.2.2.2.1, value 6 ω vals.2.2.2.2.2.2⟩,
    N, C, v, names, fn0_of_function_l hKP fn', orig, slots, vals, code⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 子类型查询沿秩层扩大保持为真

完整满足关系并不向上绝对；这里只运输子类型句子的实际较低秩见证。
先读取句子自身的类型条件，再在高层复用同一见证，最后回到同一程序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem ts_template_up_l {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
    (hX : V_d Q ν X) (hY : V_d Q μ Y) (sub : M.MemberSubset ν μ) (hwX : M.mem ω X)
    (ρ : Env (rt_model_l X ⟨⟨ω, hwX⟩⟩) 8) (hw : (ρ.bound 7).val = ω) :
    Formula.satisfies ρ ts_template_m →
      Formula.satisfies (image_env_l (N := rt_model_l Y ⟨⟨ω, ZF.v_mono_l Q hZF hX hY sub ω hwX⟩⟩)
        (fun x : {x // M.mem x X} =>
        (⟨x.val, ZF.v_mono_l Q hZF hX hY sub x.val x.property⟩ : {x // M.mem x Y})) ρ) ts_template_m := by
  let e : {x // M.mem x X} → {x // M.mem x Y} :=
    fun x => ⟨x.val, ZF.v_mono_l Q hZF hX hY sub x.val x.property⟩
  let ε := image_env_l (N := rt_model_l Y ⟨⟨ω, ZF.v_mono_l Q hZF hX hY sub ω hwX⟩⟩) e ρ
  have hwY := ZF.v_mono_l Q hZF hX hY sub ω hwX
  intro truth
  obtain ⟨hκ, hτ, hτκ, hm⟩ := ts_below_guard_l (v_transitive_l Q hX) _ (ZF.modelsKP hZF)
    ρ (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest truth
  change M.mem (ρ.bound 3).val (ρ.bound 7).val at hm
  rw [hw] at hm
  obtain ⟨C, hc⟩ := ZF.v_exists_l Q hZF hκ.1
  obtain ⟨B, U, hb, _, constants⟩ := tt_constants_exists_l hZF hc hκ hτκ
  obtain ⟨D, pool⟩ := tt_pool_exists_l Q hZF hω (ρ.bound 3).val U
  have down := ts_below_source_l hZF hω hX hwX ρ (.bound 7) (.bound 6) (.bound 5) (.bound 4)
    (.bound 3) (.bound 2) (.bound 1) .newest (Subtype.ext hw) hκ hτ hτκ hm hb constants pool
  have up := ts_below_source_l hZF hω hY hwY ε (.bound 7) (.bound 6) (.bound 5) (.bound 4)
    (.bound 3) (.bound 2) (.bound 1) .newest (Subtype.ext hw) hκ hτ hτκ hm hb constants pool
  have ⟨nm, below⟩ := down.mp truth
  exact up.mpr ⟨nm, below.mono_l hZF sub⟩

theorem Ts_program_d.up_l {ω n b a z ν μ X Y c R d S f : M.Domain} (hω : M.IsOmega ω)
    {σ : Fin 7 → M.Domain} (prog : Ts_program_d hZF ω n b σ a z)
    (hX : V_d Q ν X) (hY : V_d Q μ Y) (sub : M.MemberSubset ν μ)
    (lower : Smem_d Q c X R) (upper : Smem_d Q d Y S)
    (ff : M.IsSetFunctionFromTo Q f ω X) (fw : Rd_entry_d (σ 6) ω f) :
    Satisfies_d Q ω c a f → Satisfies_d Q ω d a f := by
  have below := ZF.v_mono_l Q hZF hX hY sub
  have hwX := ff.output_mem_of_pairMember fw
  have slot i := ff.2.2 (σ i) (hω.transitive (ZF.modelsKP hZF) b prog.length (σ i) (prog.slots i))
  obtain ⟨x₀, hx₀, fx₀⟩ := slot 0
  obtain ⟨x₁, hx₁, fx₁⟩ := slot 1
  obtain ⟨x₂, hx₂, fx₂⟩ := slot 2
  obtain ⟨x₃, hx₃, fx₃⟩ := slot 3
  obtain ⟨x₄, hx₄, fx₄⟩ := slot 4
  obtain ⟨x₅, hx₅, fx₅⟩ := slot 5
  let ρ : Env (smdl_structure_l Q (R := R) lower.1.2.1) 7 :=
    ⟨Fin.cases ⟨x₀, hx₀⟩ (Fin.cases ⟨x₁, hx₁⟩ (Fin.cases ⟨x₂, hx₂⟩ (Fin.cases ⟨x₃, hx₃⟩
      (Fin.cases ⟨x₄, hx₄⟩ (Fin.cases ⟨x₅, hx₅⟩ (fun _ => ⟨ω, hwX⟩)))))), fun _ => ⟨ω, hwX⟩⟩
  have vals : ∀ i, Rd_entry_d (σ i) (ρ.bound i).val f :=
    Fin.cases fx₀ (Fin.cases fx₁ (Fin.cases fx₂ (Fin.cases fx₃ (Fin.cases fx₄ (Fin.cases fx₅
      (Fin.cases fw (fun i => Fin.elim0 i)))))))
  let e : {x // M.mem x X} → {x // M.mem x Y} := fun x => ⟨x.val, below x.val x.property⟩
  let ρ' := image_env_l (N := smdl_structure_l Q (R := S) upper.1.2.1) e ρ
  obtain ⟨g, fg, agree⟩ := fn_recode_l Q K hZF ff
  have ffY : M.IsSetFunctionFromTo Q f ω Y := ⟨ff.1, ff.2.1,
    fun i hi => (ff.2.2 i hi).imp fun x hx => ⟨below x hx.1, hx.2⟩⟩
  have fgY : M.IsSetFunctionFromTo K g ω Y := ⟨fg.1, fg.2.1,
    fun i hi => (fg.2.2 i hi).imp fun x hx => ⟨below x hx.1, hx.2⟩⟩
  intro truth
  obtain ⟨p, code, atom⟩ := (prog.compile ν X c R f g lower ρ hX hwX ff fg agree fw vals).mp truth
  apply (prog.compile μ Y d S f g upper ρ' hY (below ω hwX) ffY fgY agree fw vals).mpr
  refine ⟨e p, code.mono_l K below, ?_⟩
  let ε : Env (rt_model_l X ⟨⟨ω, hwX⟩⟩) 8 := ⟨(ρ.push p).bound, (ρ.push p).free⟩
  have step := ts_template_up_l hZF hω hX hY sub hwX ε rfl
    ((smem_formula_l Q lower _ ts_template_m ε).mpr atom)
  have lift := (smem_formula_l Q upper ⟨⟨ω, below ω hwX⟩⟩ ts_template_m
    (image_env_l (N := rt_model_l Y ⟨⟨ω, below ω hwX⟩⟩) e ε)).mp step
  change Formula.satisfies (image_env_l (N := smdl_structure_l Q (R := S) upper.1.2.1) e (ρ.push p)) ts_template_m at lift
  have eq := @image_env_push_l (smdl_structure_l Q (R := R) lower.1.2.1)
    (smdl_structure_l Q (R := S) upper.1.2.1) e 7 ρ p
  exact (congrArg (fun ε => Formula.satisfies ε ts_template_m) eq).mp lift

end YesMetaZFC.SetTheory.Internal
