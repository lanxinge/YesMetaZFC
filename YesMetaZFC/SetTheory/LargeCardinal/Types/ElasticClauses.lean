import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Reflection.RankLargest
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 定义 3.13 的最大序数与不可达性查询

固定查询分别表示两条原句子；不把裸类型视为对逻辑推论封闭的理论。
不可达性保持当前结构中的原判断，不预先替换为背景不可达性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ee_largest_program_d (ω z : M.Domain) : Prop := M.mem z ω ∧
  ∀ n U D p, Tt_pool_d I ω n U D → Tt_code_d n U z p (Fin.elim0 : Fin 0 → M.Domain) →
    M.mem p D ∧ ∀ μ Y c R s δ t, V_d I μ Y → Smem_d I c Y R →
      Tt_realized_d I ω c Y R n s δ U D t → (M.mem p t ↔ ∃ ν, M.SuccessorOf μ ν)

def Ee_inacc_program_d (ω z : M.Domain) : Prop := M.mem z ω ∧
  ∀ n U D kw p, Tt_pool_d I ω n U D → M.mem ω U → KPair_d M kw ω ω →
    Tt_code_d n U z p (Fin.cases n (fun _ => kw) : Fin 2 → M.Domain) →
    M.mem p D ∧ ∀ c Y R s δ t, Smem_d I c Y R → Tt_realized_d I ω c Y R n s δ U D t →
      (M.mem p t ↔ Sc_inaccessible_d ω Y δ)

/-- 最大序数的程序只带 ω 和自然数码，所有参数域随后统一代入。 -/
theorem ee_largest_program_l {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ z, Ee_largest_program_d hZF ω z := by
  let φ : Formula 1 0 := .existsE (sv_max_m .newest)
  obtain ⟨z, _, _, program⟩ := tt_program_l hZF hω φ (sv_max_m_freeClosed .newest rfl)
  refine ⟨z, program.natural, fun n U D p pool code => ?_⟩
  obtain ⟨hp, read⟩ := program.query_l hZF hω pool code
  refine ⟨hp, fun μ Y c R s δ t hY model type => ?_⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨δ, type.point⟩⟩
  let ρ : Env (rt_model_l Y ny) 0 := ⟨Fin.elim0, fun _ => ⟨δ, type.point⟩⟩
  refine (read c Y R s δ t type ⟨ρ.bound, ρ.free⟩ (fun i => Fin.elim0 i)).trans
    ((smem_formula_l I model ny φ ρ).symm.trans ?_)
  simp only [φ, Formula.satisfies_exists_iff, sv_max_sat_l]
  constructor
  · rintro ⟨ν, greatest⟩
    exact ⟨ν.val, sv_max_successor_l hZF hY ny ν greatest⟩
  · rintro ⟨ν, succ⟩
    obtain ⟨A, hA⟩ := ZF.v_exists_l I hZF ((v_ordinal_l I hY).mem succ.predecessor_mem)
    exact ⟨⟨ν, ZF.v_ordinal_mem_l I hZF hY succ.predecessor_mem⟩,
      (sv_max_rank_l I hZF hA hY succ type.point _).mpr rfl⟩
/-- 不可达性的原程序同样先于任何 κ 型域取定。 -/
theorem ee_inacc_program_l {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ z, Ee_inacc_program_d hZF ω z := by
  let φ : Formula 1 2 := sc_inaccessible_m (.bound 1) .newest
  obtain ⟨z, _, _, program⟩ := tt_program_l hZF hω φ (sc_inaccessible_m_freeClosed _ _ rfl rfl)
  refine ⟨z, program.natural, fun n U D kw p pool hw pair code => ?_⟩
  obtain ⟨hp, read⟩ := program.query_l hZF hω pool code
  refine ⟨hp, fun c Y R s δ t model type => ?_⟩
  have hwY := type.constants ω hw
  let nt : Nonempty {x // M.mem x Y} := ⟨⟨ω, hwY⟩⟩
  let ρ : Env (rt_model_l Y nt) 2 := ⟨Fin.cases ⟨δ, type.point⟩ (fun _ => ⟨ω, hwY⟩), fun _ => ⟨ω, hwY⟩⟩
  refine (read c Y R s δ t type ⟨ρ.bound, ρ.free⟩
    (Fin.cases (Or.inr (Or.inl ⟨rfl, rfl⟩)) (fun _ => Or.inr (Or.inr pair)))).trans
      ((smem_formula_l I model nt φ ρ).symm.trans ?_)
  exact ⟨fun h => ⟨hwY, type.point, h⟩, fun ⟨_, _, h⟩ => h⟩

theorem ee_largest_query_l {ω n U D : M.Domain} (hω : M.IsOmega ω) (pool : Tt_pool_d I ω n U D) :
    ∃ p z, Ee_largest_program_d hZF ω z ∧ Tt_code_d n U z p (Fin.elim0 : Fin 0 → M.Domain) ∧
      M.mem p D ∧ ∀ μ Y c R s δ t, V_d I μ Y → Smem_d I c Y R →
        Tt_realized_d I ω c Y R n s δ U D t → (M.mem p t ↔ ∃ ν, M.SuccessorOf μ ν) := by
  obtain ⟨z, program⟩ := ee_largest_program_l hZF hω
  obtain ⟨p, hp, code⟩ := tt_code_l hZF hω pool program.1 (Fin.elim0 : Fin 0 → M.Domain) Fin.elim0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  exact ⟨p, z, program, code, hp, (program.2 n U D p pool code).2⟩

theorem ee_inaccessible_query_l {ω n U D : M.Domain} (hω : M.IsOmega ω) (pool : Tt_pool_d I ω n U D)
    (hw : M.mem ω U) : ∃ p z kw, Ee_inacc_program_d hZF ω z ∧ KPair_d M kw ω ω ∧
      Tt_code_d n U z p (Fin.cases n (fun _ => kw) : Fin 2 → M.Domain) ∧
      M.mem p D ∧ ∀ c Y R s δ t, Smem_d I c Y R →
        Tt_realized_d I ω c Y R n s δ U D t → (M.mem p t ↔ Sc_inaccessible_d ω Y δ) := by
  obtain ⟨z, program⟩ := ee_inacc_program_l hZF hω
  obtain ⟨kw, pair⟩ := (I).total ω ω
  obtain ⟨e, he⟩ := num_exists_l (ZF.modelsKP hZF) 0
  obtain ⟨i, hi⟩ := num_exists_l (ZF.modelsKP hZF) 1
  obtain ⟨p, hp, code⟩ := tt_code_l hZF hω pool program.1 (Fin.cases e (fun _ => i) : Fin 2 → M.Domain)
    (Fin.cases n (fun _ => kw)) (Fin.cases he (Fin.cases hi (fun j => Fin.elim0 j)))
    (Fin.cases (Or.inr (Or.inl rfl)) (fun _ => Or.inr (Or.inr ⟨ω, hw, pair⟩)))
  exact ⟨p, z, kw, program, pair, code, hp, (program.2 n U D kw p pool hw pair code).2⟩

end YesMetaZFC.SetTheory.LargeCardinal
