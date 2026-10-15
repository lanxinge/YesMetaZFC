import YesMetaZFC.SetTheory.LargeCardinal.TypeGameResetMove
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericCapture

/-! # 原辅助轮开始时的有限状态与可继续性

状态保存实际三阶段时钟、已落下的实数图和前一个请求。由武丁重置构造直接
证明每个这样的状态都有合法请求；不把“存在下一步”加入递归的假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_ready_d (p : Tg_params_d M.Domain) (X n h : M.Domain) : Prop :=
  M.mem n p.ω ∧ ∃ i z, M.mem i p.ω ∧ Fn0_d i X h ∧ M.IsOrdinalDivision I i p.c n p.e ∧
    Tg_digits_d hZF p.c p.b n p.A h z ∧
    (n = p.e ∨ ∃ j a ℓ t κ u, M.SuccessorOf n j ∧ Tg_event_d I p.c j p.e h a ∧ Tg_aux_data_d a ℓ t κ u ∧ M.mem κ p.δ)

def tg_ready_m {d} (ω e c b δ A X n h : Term d) : Formula 1 d := set[d] ⟪⌜n⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∃ i z, i ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(i, ⌜X⌝ₛ, ⌜h⌝ₛ) ∧
    ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜e⌝ₛ) ∧
    ⌜tg_digits_m⌝ₚ(⌜c⌝ₛ, ⌜b⌝ₛ, ⌜n⌝ₛ, ⌜A⌝ₛ, ⌜h⌝ₛ, z) ∧
    (⌜n⌝ₛ = ⌜e⌝ₛ ∨ (∃ j a ℓ t κ u, ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ, j) ∧
      ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, j, ⌜e⌝ₛ, ⌜h⌝ₛ, a) ∧ ⌜tg_aux_data_m⌝ₚ(a, ℓ, t, κ, u) ∧ κ ∈ ⌜δ⌝ₛ)))⟫
derive_free_closed tg_ready_m

theorem tg_ready_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X n h : Term d) :
    Formula.satisfies ρ (tg_ready_m p.ω p.e p.c p.b p.δ p.A X n h) ↔
      Tg_ready_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (n.eval ρ) (h.eval ρ) := by
  simp only [tg_ready_m, Tg_ready_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, fn0_sat_l hZF.1, Formula.satisfies_isOrdinalDivision_iff I hZF.1,
    tg_digits_sat_l hZF, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hZF.1, tg_aux_data_sat_l hZF.1,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]; rfl

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

theorem Tg_setup_d.ready_empty_l {p : Tg_params_d M.Domain} {X : M.Domain}
    (setup : Tg_setup_d hZFC p X) : Tg_ready_d hZ p X p.e p.e := by
  have he := num_mem_l hZ.1 setup.omega (show Num_d 0 p.e from setup.empty)
  have oe := setup.omega.members_areOrdinals hZ p.e he
  obtain ⟨hc, _⟩ := tg_clock_l hZ setup.omega setup.empty setup.one setup.two setup.three he
  have oc := setup.omega.members_areOrdinals hZ p.c hc
  have ec := oc.empty_mem_of_nonempty (ZF.modelsKP hZ) ⟨p.b, setup.three.predecessor_mem⟩ setup.empty
  have empty (Y : M.Domain) : Fn0_d p.e Y p.e := ⟨fun x hx => (setup.empty x hx).elim,
    fun x hx => (setup.empty x hx).elim, fun x hx => (setup.empty x hx).elim⟩
  exact ⟨he, p.e, p.e, he, empty X, ⟨oe, ec, p.e,
    (ZF.ordinalMultiplication_zero_iff hZ K oc setup.empty).mpr setup.empty,
    (ZF.ordinalAddition_zero_iff hZ K setup.empty).mpr rfl⟩,
    ⟨empty p.A, fun i _ hi => (setup.empty i hi).elim⟩, Or.inl rfl⟩

/-- 可继续性来自原重置类型工厂，包括零轮的字母表秩界和后继轮的参数域增长。 -/
theorem Tg_setup_d.ready_move_l {p : Tg_params_d M.Domain} {X n h : M.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d K p.δ) (root : M.mem p.e p.S)
    (ready : Tg_ready_d hZ p X n h) : ∃ a, M.mem a X ∧ Tg_aux_d hZ p n h a := by
  obtain ⟨_, i, z, _, _, _, digits, old⟩ := ready
  have heω := num_mem_l hZ.1 setup.omega (show Num_d 0 p.e from setup.empty)
  have zero := setup.limit.1.transitive p.ω setup.above p.e heω
  have bound : ∃ τ, M.mem τ p.δ ∧ (n = p.e ∨ ∃ j a ℓ t u,
      M.SuccessorOf n j ∧ Tg_event_d K p.c j p.e h a ∧ Tg_aux_data_d a ℓ t τ u) := by
    rcases old with eq | ⟨j, a, ℓ, t, τ, u, succ, event, data, below⟩
    · exact ⟨p.e, zero, Or.inl eq⟩
    · exact ⟨τ, below, Or.inr ⟨j, a, ℓ, t, u, succ, event, data⟩⟩
  obtain ⟨τ, hτ, old⟩ := bound
  obtain ⟨B, hB, pair⟩ := (sc_v_algebra_l hZFC setup.limit setup.rank).pair p.A τ setup.letters
    (ZF.v_ordinal_mem_l K hZ setup.rank hτ)
  obtain ⟨χ, Z, hχ, hZ', sub⟩ := (ZF.v_unfold_l K hZ setup.rank B).mp hB
  have hAZ := sub p.A ((pair p.A).mpr (Or.inl rfl))
  have hτχ := ZF.v_ordinal_height_l hZ hZ' (setup.limit.1.mem hτ) (sub τ ((pair τ).mpr (Or.inr rfl)))
  obtain ⟨κ, C, a, u, above, _, rank, ha, _, legal⟩ := setup.reset_move_l hZFC hd root hχ
  refine ⟨a, ha, legal n h z digits ?_⟩
  rcases old with eq | ⟨j, v, ℓ, t, u, succ, event, data⟩
  · exact Or.inl ⟨eq, ZF.v_mono_l K hZ hZ' rank ((v_ordinal_l K rank).transitive χ above) p.A hAZ⟩
  · exact Or.inr ⟨j, v, ℓ, t, τ, u, succ, event, data, (v_ordinal_l K rank).transitive χ above τ hτχ⟩

end YesMetaZFC.SetTheory.LargeCardinal
