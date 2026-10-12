import YesMetaZFC.Model.SetTheory.Internal.TypePackedQuery
import YesMetaZFC.Model.SetTheory.Internal.SubtypeWitness
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # 子类型的同一固定查询与完整实现

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
        · exact (fill.2 i x).mpr ⟨hω.transitive hZF n prog.finite i hi, Or.inl ⟨hi, hx⟩⟩
        · exact ((fill.2 i x).mp hx).2.elim And.right (fun h => (h.1 hi).elim)
      exact orig.trans (agree i x).symm
    obtain ⟨p, hp, cp, below⟩ := (ts_prefix_l hZF hω hY prog.finite hwV fg same).mpr real
    exact ⟨g, fg, same, ⟨p, hp⟩, cp, (atom ⟨p, hp⟩).mpr ⟨nm, below⟩⟩

end YesMetaZFC.SetTheory.Internal
