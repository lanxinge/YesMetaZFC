import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Reflection.RankLargest
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Types.CanonicalSatisfaction
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Types.Minus
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence

/-! # 前驱定义域的实际内部公式

先合取任意内部有限组变量的成员断言，再追加原公式“X=Vν，其中 ν 最大”，
最后绑定 X。程序本身不依赖实现元组、背景秩层或任何真值假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 原变量数来自内部 ω；前一层只是新绑定变量，未增添类型常量。 -/
theorem sg_guard_build_l (hZF : M.Models ZF) {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ a m G u, Sformula_d I ω a m G u ∧
      ∀ c Y R (hm : Smem_d I c Y R) f, M.IsSetFunctionFromTo I f ω Y →
        (Satisfies_d I ω c a f ↔ ∃ X, ∃ hx : M.mem X Y,
          Formula.satisfies (⟨fun _ => ⟨X, hx⟩, fun _ => ⟨X, hx⟩⟩ :
            Env (smdl_structure_l I (R := R) hm.1.2.1) 1) (sv_last_m .newest) ∧
          ∀ i y, M.mem i n → M.PairMember I i y f → M.mem y X) := by
  obtain ⟨m, G, u, hG, hu, all⟩ := sg_all_build_l I hZF hω hn hn
  obtain ⟨b, succ, hb⟩ := hω.1.2 n hn
  let φ : Formula 1 1 := sv_last_m .newest
  have hc : φ.FreeClosed := sv_last_m_freeClosed _ rfl
  obtain ⟨m₁, G₁, v, add, compile⟩ := source_compile_core_l I hZF hω (source_core_l φ)
    (source_core_closed_l φ hc) (fun _ => n) hb (fun _ => succ.predecessor_mem) hG
  obtain ⟨m₂, G₂, w, conj, both⟩ := sfm_and_l I hZF hω add.program (add.span u hu) add.root
  obtain ⟨l, H, r, ex, quant⟩ := sfm_ex_l I hZF hω conj.program hn conj.root
  obtain ⟨a, ca⟩ := I.total H r
  have form : Sformula_d I ω a l H r := ⟨ca, ex.program, ex.root⟩
  refine ⟨a, l, H, r, form, fun c Y R hm f fn => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω Y
  have hf := (hE f).mpr fn
  have body X (hx : M.mem X Y) g (update : Senv_update_d I f n X g) :
      Ssat_d I Y R E G₂ m₂ w g ↔
        Formula.satisfies (⟨fun _ => ⟨X, hx⟩, fun _ => ⟨X, hx⟩⟩ :
          Env (smdl_structure_l I (R := R) hm.1.2.1) 1) φ ∧
          ∀ i y, M.mem i n → M.PairMember I i y f → M.mem y X := by
    have fg := update.function_l I fn hn hx
    have hg := (hE g).mpr fg
    have hbg := (update.2 n X).mpr (Or.inl ⟨rfl, rfl⟩)
    have agree := update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) n)
    let ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) 1 := ⟨fun _ => ⟨X, hx⟩, fun _ => ⟨X, hx⟩⟩
    have base := (compile Y R hm.1.2.1 E hE g hg ρ (fun _ => hbg)).trans (source_core_sat_l φ ρ)
    have old := (add.sat_l I hZF hG hu Y R E g).symm.trans (all Y R E g X hE hg hbg)
    refine (both Y R E g hg).trans ((and_congr old base).trans ⟨?_, ?_⟩)
    · rintro ⟨members, truth⟩
      exact ⟨truth, fun i y hi he => ((hm.2 y X).mp (members i y hi ((agree i y hi).mp he))).2.2⟩
    · rintro ⟨truth, members⟩
      exact ⟨fun i y hi he => (hm.2 y X).mpr ⟨fg.output_mem_of_pairMember he, hx,
        members i y hi ((agree i y hi).mpr he)⟩, truth⟩
  refine (satisfies_decode_l I hZF.1 hm.1 form hE).trans ((quant Y R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨X, g, hx, update, truth⟩
    exact ⟨X, hx, (body X hx g update).mp truth⟩
  · rintro ⟨X, hx, truth⟩
    obtain ⟨g, update, _⟩ := senv_update_exists_l I hZF fn hn hx
    exact ⟨X, g, hx, update, (body X hx g update).mpr truth⟩

/-- 在后继秩层上，该实际公式恰检查所有原变量是否属于前一层。 -/
theorem sg_guard_rank_l (hZF : M.Models ZF) {ω n : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ a m G u, Sformula_d I ω a m G u ∧
      ∀ ν μ X Y c R f, V_d I ν X → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
        Smem_d I c Y R → M.IsSetFunctionFromTo I f ω Y →
        (Satisfies_d I ω c a f ↔ ∀ i y, M.mem i n → M.PairMember I i y f → M.mem y X) := by
  obtain ⟨a, m, G, u, form, guard⟩ := sg_guard_build_l I hZF hω hn
  refine ⟨a, m, G, u, form, fun ν μ X Y c R f hV hW hs hων hm fn => ?_⟩
  have pow := ZF.v_successor_l I hZF hV hW hs
  have hXY := (pow X).mpr (fun _ h => h)
  have hwY := (pow ω).mpr (fun i hi => ZF.v_ordinal_mem_l I hZF hV (hων i hi))
  let N := rt_model_l Y ⟨⟨ω, hwY⟩⟩
  have last Z (hZ : M.mem Z Y) :
      Formula.satisfies (⟨fun _ => ⟨Z, hZ⟩, fun _ => ⟨Z, hZ⟩⟩ :
        Env (smdl_structure_l I (R := R) hm.1.2.1) 1) (sv_last_m .newest) ↔ Z = X := by
    let ρ : Env N 1 := ⟨fun _ => ⟨Z, hZ⟩, fun _ => ⟨Z, hZ⟩⟩
    exact (smem_formula_l I hm ⟨⟨ω, hwY⟩⟩ (sv_last_m .newest) ρ).symm.trans
      (sv_last_rank_l I hZF hω hV hW hs hwY ρ .newest)
  refine (guard c Y R hm f fn).trans ⟨?_, ?_⟩
  · rintro ⟨Z, hZ, hz, all⟩
    exact (last Z hZ).mp hz ▸ all
  · intro all
    exact ⟨X, hXY, (last X hXY).mpr rfl, all⟩

/-- 自然数码的读取只依赖 ω 和程序元数，与具体 κ 常量无关。 -/
def Tg_guard_program_d (ω l z : M.Domain) : Prop := M.mem l ω ∧ M.mem z ω ∧
  ∀ ν μ X Y c R f, V_d I ν X → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
    Smem_d I c Y R → M.IsSetFunctionFromTo I f ω Y →
      (Sc_sat_d I ω c z f ↔ ∀ i y, M.mem i l → M.PairMember I i y f → M.mem y X)

theorem tg_guard_program_l (hZF : M.Models ZF) {ω l : M.Domain}
    (hω : M.IsOmega ω) (hl : M.mem l ω) : ∃ z, Tg_guard_program_d I ω l z := by
  obtain ⟨a, m, G, u, form, guard⟩ := sg_guard_rank_l I hZF hω hl
  obtain ⟨z, code⟩ := sc_num_exists_l I hZF hω form
  exact ⟨z, hl, sc_num_natural_l I hZF hω code, fun ν μ X Y c R f hX hY succ bound model fn =>
    (sc_sat_decode_l I hZF hω code).trans (guard ν μ X Y c R f hX hY succ bound model fn)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 前驱定义域的完整类型查询

实际查询只依赖变量数和集合常量 κ，与实现元组和秩层无关。
查询成员性精确检查 κ、δ 及所有原变量是否属于最大序数对应的前一层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 读取指定的原程序和原名字列，不重新选择查询。 -/
theorem Tg_guard_program_d.query_l {ω n κ U D l z p : M.Domain} (hω : M.IsOmega ω)
    (program : Tg_guard_program_d I ω l z) (pool : Tt_pool_d I ω n U D)
    (code : Tg_guard_code_d n κ U l z p) : M.mem p D ∧
    ∀ ν μ X Y c R s δ t, V_d I ν X → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
      Smem_d I c Y R → Tt_realized_d I ω c Y R n s δ U D t →
      (M.mem p t ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X) := by
  obtain ⟨b, k, e, N, hb, hl, names, fn₀, hk, hp, old, last⟩ := code
  obtain ⟨N', E, names', seq, prod⟩ := pool
  have eq := hZF.1.eq_of_same_members N' N (fun x => (names' x).trans (names x).symm)
  subst N'
  have fn := fn0_function_l (ZF.modelsKP hZF) fn₀
  have hpD := (prod p).mpr ⟨z, program.2.1, e, (seq e).mpr ⟨l, program.1, fn⟩, hp⟩
  have column i a : Rd_entry_d i a e ↔ (M.mem i b ∧ a = i) ∨ (i = b ∧ a = k) := by
    refine ⟨fun entry => ?_, fun h => h.elim (fun ⟨hi, eq⟩ => eq.symm ▸ old i hi)
      (fun ⟨eq, eq'⟩ => eq.symm ▸ eq'.symm ▸ last)⟩
    rcases (hl i).mp (fn.input_mem_of_pairMember entry) with hi | eq
    exact Or.inl ⟨hi, fn.1.2 i a i entry (old i hi)⟩
    have eq := hZF.1.eq_of_same_members i b eq
    exact Or.inr ⟨eq, fn.1.2 i a k entry (eq.symm ▸ last)⟩
  refine ⟨hpD, fun ν μ X Y c R s δ t hV hW hs hων hm type => ?_⟩
  obtain ⟨v, assign, fv⟩ := tn_assign_exists_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) n type.finite)
    type.tuple type.point type.constants names (fn0_of_function_l (ZF.modelsKP hZF) fn)
  obtain ⟨f, fill, ff⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fv) type.point
  exact (type.truth p).trans ((and_iff_right hpD).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) hp program.2.1 program.1 fn.2.1 assign fill).trans
      ((program.2.2 ν μ X Y c R f hV hW hs hων hm ff).trans
        (tg_column_values_l hZF hω hb hl program.1 hk column type.tuple assign fill ff))))

/-- 程序元数和自然数码与原查询一起返回，供跨模型保持。 -/
theorem tt_guard_query_l {ω n κ U D : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.mem κ U) (pool : Tt_pool_d I ω n U D) :
    ∃ p l z, Tg_guard_program_d I ω l z ∧ Tg_guard_code_d n κ U l z p ∧ M.mem p D ∧
      ∀ ν μ X Y c R s δ t, V_d I ν X → V_d I μ Y → M.SuccessorOf μ ν → M.MemberSubset ω ν →
        Smem_d I c Y R → Tt_realized_d I ω c Y R n s δ U D t →
        (M.mem p t ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X) := by
  obtain ⟨N, E, names, seq, prod⟩ := pool
  obtain ⟨b, l, k, e, hb, hl, hlω, hk, fn, column⟩ := tg_column_l hZF hω hn hκ names
  obtain ⟨z, program⟩ := tg_guard_program_l I hZF hω hlω
  obtain ⟨p, hp⟩ := (I).total z e
  have hpD := (prod p).mpr ⟨z, program.2.1, e, (seq e).mpr ⟨l, hlω, fn⟩, hp⟩
  have code : Tg_guard_code_d n κ U l z p := ⟨b, k, e, N, hb, hl, names,
    fn0_of_function_l (ZF.modelsKP hZF) fn, hk, hp,
    fun i hi => (column i i).mpr (Or.inl ⟨hi, rfl⟩), (column b k).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  exact ⟨p, l, z, program, code, program.query_l hZF hω ⟨N, E, names, seq, prod⟩ code⟩

/-- 实际定义域查询是前驱实现的充分必要条件；常量域的下降从 κ 的下降自动推出。 -/
theorem tt_minus_guarded_l {ω ν μ κ B X Y c R n s δ U D t : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hW : V_d I μ Y) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hB : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (hm : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n s δ U D t) :
    ∃ p, M.mem p D ∧ (M.mem p t ↔ Fn0_d n X s ∧ M.mem δ X ∧ M.mem κ X) ∧
      (M.mem p t ↔ ∃ d S u, Smem_d I d X S ∧ Tm_minus_d I ω D t u ∧
        Tt_realized_d I ω d X S n s δ U D u) := by
  obtain ⟨p, _, _, _, _, hp, read⟩ := tt_guard_query_l hZF hω type.finite ((constants κ).mpr (Or.inr rfl)) type.pool
  have guard := read ν μ X Y c R s δ t hV hW hs hων hm type
  refine ⟨p, hp, guard, ⟨?_, ?_⟩⟩
  · intro ht
    obtain ⟨tuple, point, critical⟩ := guard.mp ht
    have hκν := ZF.v_ordinal_height_l hZF hV (v_ordinal_l I hB) critical
    have sub := ZF.v_mono_l I hZF hB hV ((v_ordinal_l I hV).transitive κ hκν)
    exact tt_minus_rank_l hZF hω hV hW hs type hm tuple point (fun x hx =>
      ((constants x).mp hx).elim (sub x) (fun eq => eq.symm ▸ critical))
  · rintro ⟨_, _, _, _, _, lower⟩
    exact guard.mpr ⟨lower.tuple, lower.point, lower.constants κ ((constants κ).mpr (Or.inr rfl))⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 查询程序及原名字列的有限公式

字面编码只记录实际列图和坐标。自然数程序的全称正确性单独保存，
从而既能固定低程序，也能在共同秩段中读取含新常量的原名字列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tt_code0_m {d} (n U z p : Term d) : Formula 1 d := set[d] ⟪∃ N C b,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜num0_m 0⌝ₚ(b) ∧ ⌜fn0_m⌝ₚ(b, N, C) ∧ ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜z⌝ₛ, C)⟫
derive_free_closed tt_code0_m

def tt_code2_m {d} (n U z p a b : Term d) : Formula 1 d := set[d] ⟪∃ N C l,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜num0_m 2⌝ₚ(l) ∧ ⌜fn0_m⌝ₚ(l, N, C) ∧ ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜z⌝ₛ, C) ∧
  (∀ i ∈ l, ⌜num0_m 0⌝ₚ(i) → ⌜rd_entry0_m⌝ₚ(i, ⌜a⌝ₛ, C)) ∧
  (∀ i ∈ l, ⌜num0_m 1⌝ₚ(i) → ⌜rd_entry0_m⌝ₚ(i, ⌜b⌝ₛ, C))⟫
derive_free_closed tt_code2_m

def tg_guard_code_m {d} (n κ U l z p : Term d) : Formula 1 d := set[d] ⟪∃ b k C N,
  ⌜KP.succ0_m⌝ₚ(b, ⌜n⌝ₛ) ∧ ⌜KP.succ0_m⌝ₚ(⌜l⌝ₛ, b) ∧ ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧
  ⌜fn0_m⌝ₚ(⌜l⌝ₛ, N, C) ∧ ⌜kpair0_m⌝ₚ(k, ⌜κ⌝ₛ, ⌜κ⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜z⌝ₛ, C) ∧
  (∀ i ∈ b, ⌜rd_entry0_m⌝ₚ(i, i, C)) ∧ ⌜rd_entry0_m⌝ₚ(b, k, C)⟫
derive_free_closed tg_guard_code_m

def tg_guard_program0_m : Formula 1 3 :=
  let ω : Term 3 := .bound 0
  let l : Term 3 := .bound 1
  let z : Term 3 := .bound 2
  set[3] ⟪⌜l⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∀ ν μ X Y c R f, ⌜v_m kpair_convention_l⌝ₚ(ν, X) → ⌜v_m kpair_convention_l⌝ₚ(μ, Y) →
    ⌜Formula.isSuccessor⌝ₚ(μ, ν) → ⌜ω⌝ₛ ⊆ ν → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
    ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(f, ⌜ω⌝ₛ, Y) →
      (⌜sc_sat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c, ⌜z⌝ₛ, f) ↔
        ∀ i y, i ∈ ⌜l⌝ₛ → ⌜rd_entry0_m⌝ₚ(i, y, f) → y ∈ X))⟫
theorem tg_guard_program0_closed_l : tg_guard_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_guard_program0_m, Definitional.Formula.FreeClosed]

def tg_guard_program_m {d} (ω l z : Term d) : Formula 1 d :=
  tg_guard_program0_m.bind (Fin.cases ω (Fin.cases l (fun _ => z)))

@[simp] theorem tg_guard_program_closed_l {d} (ω l z : Term d)
    (hw : ω.freeSupport = []) (hl : l.freeSupport = []) (hz : z.freeSupport = []) :
    (tg_guard_program_m ω l z).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hw (Fin.cases hl (fun _ => hz))) _).mpr tg_guard_program0_closed_l

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
include hKP

theorem tt_code0_sat_l {d} (ρ : Env M d) (n U z p : Term d) :
    Formula.satisfies ρ (tt_code0_m n U z p) ↔
      Tt_code_d (n.eval ρ) (U.eval ρ) (z.eval ρ) (p.eval ρ) (Fin.elim0 : Fin 0 → M.Domain) := by
  simp only [tt_code0_m, Tt_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tn_names0_sat_l hKP, num0_sat_l hKP.1, fn0_sat_l hKP.1, kpair0_sat_l hKP.1,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨N, C, b, names, hb, fn, pair⟩ => ⟨N, C, b, names, hb, fn, pair, fun i => Fin.elim0 i⟩,
    fun ⟨N, C, b, names, hb, fn, pair, _⟩ => ⟨N, C, b, names, hb, fn, pair⟩⟩

theorem tt_code2_sat_l {d} (ρ : Env M d) (n U z p a b : Term d) :
    Formula.satisfies ρ (tt_code2_m n U z p a b) ↔
      Tt_code_d (n.eval ρ) (U.eval ρ) (z.eval ρ) (p.eval ρ)
        (Fin.cases (a.eval ρ) (fun _ => b.eval ρ) : Fin 2 → M.Domain) := by
  simp only [tt_code2_m, Tt_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, tn_names0_sat_l hKP,
    num0_sat_l hKP.1, fn0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨N, C, l, names, hl, fn, pair, ha, hb⟩ =>
    ⟨N, C, l, names, hl, fn, pair,
      Fin.cases (fun x hx => ha x (num_lt_l hKP.1 hx hl (by decide)) hx)
        (Fin.cases (fun x hx => hb x (num_lt_l hKP.1 hx hl (by decide)) hx) (fun i => Fin.elim0 i))⟩,
    fun ⟨N, C, l, names, hl, fn, pair, params⟩ =>
      ⟨N, C, l, names, hl, fn, pair, fun x _ => params 0 x, fun x _ => params 1 x⟩⟩

theorem tg_guard_code_sat_l {d} (ρ : Env M d) (n κ U l z p : Term d) :
    Formula.satisfies ρ (tg_guard_code_m n κ U l z p) ↔
      Tg_guard_code_d (n.eval ρ) (κ.eval ρ) (U.eval ρ) (l.eval ρ) (z.eval ρ) (p.eval ρ) := by
  simp only [tg_guard_code_m, Tg_guard_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.succ0_sat_l hKP.1, tn_names0_sat_l hKP, fn0_sat_l hKP.1, kpair0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]
  rfl

theorem tg_guard_program_sat_l {d} (ρ : Env M d) (ω l z : Term d) :
    Formula.satisfies ρ (tg_guard_program_m ω l z) ↔ Tg_guard_program_d I (ω.eval ρ) (l.eval ρ) (z.eval ρ) := by
  simp only [tg_guard_program_m, Formula.satisfies_bind, tg_guard_program0_m, Tg_guard_program_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, v_sat_l I hKP.1, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_subset_iff, smem_sat_l I, Formula.satisfies_isFunctionFromTo_iff I hKP.1,
    Formula.satisfies_iff_iff, sc_sat_formula_l I hKP.1,
    rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 原查询名字列的向上读取

只解包原存在见证，再传输有界矩阵；源不需要满足 KP。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
include hKP hX

theorem tt_code0_source_l {d} (ρ : Env N d) (n U z p : Term d)
    (valid : Formula.satisfies ρ (tt_code0_m n U z p)) :
    Tt_code_d (n.eval ρ).val (U.eval ρ).val (z.eval ρ).val (p.eval ρ).val (Fin.elim0 : Fin 0 → M.Domain) := by
  simp only [tt_code0_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨A, C, b, matrix⟩ := valid
  have up := (rt_model_delta_l hX nx
    (.conj (tn_names0_delta_l ..) (.conj (num0_delta_l 0 _) (.conj (fn0_delta_l ..) (kpair0_delta_l ..)))) _).mp matrix
  have full : Formula.satisfies (image_env_l Subtype.val ρ) (tt_code0_m n U z p) := by
    simp only [tt_code0_m, Formula.satisfies_exists_iff]
    exact ⟨A.val, C.val, b.val, by simpa only [@image_env_push_l N M Subtype.val] using up⟩
  simpa only [@eval_image_env_l N M Subtype.val] using (tt_code0_sat_l hKP _ _ _ _ _).mp full

theorem tt_code2_source_l {d} (ρ : Env N d) (n U z p a b : Term d)
    (valid : Formula.satisfies ρ (tt_code2_m n U z p a b)) :
    Tt_code_d (n.eval ρ).val (U.eval ρ).val (z.eval ρ).val (p.eval ρ).val
      (Fin.cases (a.eval ρ).val (fun _ => (b.eval ρ).val) : Fin 2 → M.Domain) := by
  simp only [tt_code2_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨A, C, l, matrix⟩ := valid
  have up := (rt_model_delta_l hX nx (.conj (tn_names0_delta_l ..) (.conj (num0_delta_l 2 _)
    (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj
      (.forallMem _ (.imp (num0_delta_l 0 _) (rd_entry0_delta_l ..)))
      (.forallMem _ (.imp (num0_delta_l 1 _) (rd_entry0_delta_l ..)))))))) _).mp matrix
  have full : Formula.satisfies (image_env_l Subtype.val ρ) (tt_code2_m n U z p a b) := by
    simp only [tt_code2_m, Formula.satisfies_exists_iff]
    exact ⟨A.val, C.val, l.val, by simpa only [@image_env_push_l N M Subtype.val] using up⟩
  simpa only [@eval_image_env_l N M Subtype.val] using (tt_code2_sat_l hKP _ _ _ _ _ _ _).mp full

theorem tg_guard_code_source_l {d} (ρ : Env N d) (n κ U l z p : Term d)
    (valid : Formula.satisfies ρ (tg_guard_code_m n κ U l z p)) :
    Tg_guard_code_d (n.eval ρ).val (κ.eval ρ).val (U.eval ρ).val (l.eval ρ).val (z.eval ρ).val (p.eval ρ).val := by
  simp only [tg_guard_code_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨b, k, C, A, matrix⟩ := valid
  have up := (rt_model_delta_l hX nx (.conj (KP.succ0_delta_l ..) (.conj (KP.succ0_delta_l ..)
    (.conj (tn_names0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..)
      (.conj (kpair0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..)) (rd_entry0_delta_l ..)))))))) _).mp matrix
  have full : Formula.satisfies (image_env_l Subtype.val ρ) (tg_guard_code_m n κ U l z p) := by
    simp only [tg_guard_code_m, Formula.satisfies_exists_iff]
    exact ⟨b.val, k.val, C.val, A.val, by simpa only [@image_env_push_l N M Subtype.val] using up⟩
  simpa only [@eval_image_env_l N M Subtype.val] using (tg_guard_code_sat_l hKP _ _ _ _ _ _ _).mp full

end YesMetaZFC.SetTheory.Internal

/-! ## 同一查询名字列回到传递源

列图和槽位由原查询对回收，完整名字域由源内构造给出。
因此程序码和查询都不改变；反射只检查有界矩阵。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
include hKP hX

theorem tt_code0_reflect_l {ω : M.Domain} (hω : M.IsOmega ω) (hw : M.mem ω X)
    {d} (ρ : Env N d) (n U z p : Term d) {A : M.Domain} (hA : M.mem A X)
    (names : Tn_names_d (n.eval ρ).val (U.eval ρ).val A)
    (code : Tt_code_d (n.eval ρ).val (U.eval ρ).val (z.eval ρ).val (p.eval ρ).val (Fin.elim0 : Fin 0 → M.Domain)) :
    Formula.satisfies ρ (tt_code0_m n U z p) := by
  obtain ⟨A', C, b, names', nb, fn, pair, _⟩ := code
  have eq := hKP.1.eq_of_same_members A' A (fun x => (names' x).trans (names x).symm)
  subst A'
  let a₀ : (N).Domain := ⟨A, hA⟩
  let c₀ : (N).Domain := ⟨C, (pair.mem_l M hX (p.eval ρ).property).2⟩
  let b₀ : (N).Domain := ⟨b, hX ω hw b (num_mem_l hKP.1 hω nb)⟩
  simp only [tt_code0_m, Formula.satisfies_exists_iff]
  refine ⟨a₀, c₀, b₀, ?_⟩
  apply (rt_model_delta_l hX nx
    (.conj (tn_names0_delta_l ..) (.conj (num0_delta_l 0 _) (.conj (fn0_delta_l ..) (kpair0_delta_l ..)))) _).mpr
  simp only [Formula.satisfies_conj_iff, tn_names0_sat_l hKP, num0_sat_l hKP.1, fn0_sat_l hKP.1,
    kpair0_sat_l hKP.1, @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨names, nb, fn, pair⟩

theorem tt_code2_reflect_l {ω : M.Domain} (hω : M.IsOmega ω) (hw : M.mem ω X)
    {d} (ρ : Env N d) (n U z p a b : Term d) {A : M.Domain} (hA : M.mem A X)
    (names : Tn_names_d (n.eval ρ).val (U.eval ρ).val A)
    (code : Tt_code_d (n.eval ρ).val (U.eval ρ).val (z.eval ρ).val (p.eval ρ).val
      (Fin.cases (a.eval ρ).val (fun _ => (b.eval ρ).val) : Fin 2 → M.Domain)) :
    Formula.satisfies ρ (tt_code2_m n U z p a b) := by
  obtain ⟨A', C, l, names', nl, fn, pair, slots⟩ := code
  have eq := hKP.1.eq_of_same_members A' A (fun x => (names' x).trans (names x).symm)
  subst A'
  let a₀ : (N).Domain := ⟨A, hA⟩
  let c₀ : (N).Domain := ⟨C, (pair.mem_l M hX (p.eval ρ).property).2⟩
  let l₀ : (N).Domain := ⟨l, hX ω hw l (num_mem_l hKP.1 hω nl)⟩
  simp only [tt_code2_m, Formula.satisfies_exists_iff]
  refine ⟨a₀, c₀, l₀, ?_⟩
  apply (rt_model_delta_l hX nx (.conj (tn_names0_delta_l ..) (.conj (num0_delta_l 2 _)
    (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj
      (.forallMem _ (.imp (num0_delta_l 0 _) (rd_entry0_delta_l ..)))
      (.forallMem _ (.imp (num0_delta_l 1 _) (rd_entry0_delta_l ..)))))))) _).mpr
  simp only [Formula.satisfies_conj_iff, tn_names0_sat_l hKP, num0_sat_l hKP.1, fn0_sat_l hKP.1,
    kpair0_sat_l hKP.1, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1,
    @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨names, nl, fn, pair, fun i _ => slots 0 i, fun i _ => slots 1 i⟩

theorem tg_guard_code_reflect_l {d} (ρ : Env N d) (n κ U l z p : Term d)
    {A : M.Domain} (hA : M.mem A X) (names : Tn_names_d (n.eval ρ).val (U.eval ρ).val A)
    (code : Tg_guard_code_d (n.eval ρ).val (κ.eval ρ).val (U.eval ρ).val (l.eval ρ).val (z.eval ρ).val (p.eval ρ).val) :
    Formula.satisfies ρ (tg_guard_code_m n κ U l z p) := by
  obtain ⟨b, k, C, A', hb, hl, names', fn, pair, cp, old, last⟩ := code
  have eq := hKP.1.eq_of_same_members A' A (fun x => (names' x).trans (names x).symm)
  subst A'
  have hC := (cp.mem_l M hX (p.eval ρ).property).2
  let b₀ : (N).Domain := ⟨b, hX (l.eval ρ).val (l.eval ρ).property b hl.predecessor_mem⟩
  let k₀ : (N).Domain := ⟨k, (rd_entry_transitive_l hX hC last).2⟩
  let c₀ : (N).Domain := ⟨C, hC⟩
  let a₀ : (N).Domain := ⟨A, hA⟩
  simp only [tg_guard_code_m, Formula.satisfies_exists_iff]
  refine ⟨b₀, k₀, c₀, a₀, ?_⟩
  apply (rt_model_delta_l hX nx (.conj (KP.succ0_delta_l ..) (.conj (KP.succ0_delta_l ..)
    (.conj (tn_names0_delta_l ..) (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..)
      (.conj (kpair0_delta_l ..) (.conj (.forallMem _ (rd_entry0_delta_l ..)) (rd_entry0_delta_l ..)))))))) _).mpr
  simp only [Formula.satisfies_conj_iff, KP.succ0_sat_l hKP.1, tn_names0_sat_l hKP, fn0_sat_l hKP.1,
    kpair0_sat_l hKP.1, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hKP.1,
    @eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨hb, hl, names, fn, pair, cp, old, last⟩

end YesMetaZFC.SetTheory.Internal
