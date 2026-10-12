import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticSyntax
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleSyntax

/-! # 四条弹性查询的统一读取公式

固定代码先于所有实现取定；全称读取同时覆盖全部内部元数的实际元组。
伸展仍是同一扩展器的原超幂关系，源证书由公式自身的前件完整检查。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ee_read_d (ω κ n U D : M.Domain) (q : Ee_queries_d M) : Prop :=
  ∀ ν μ A Y X c R δ K S s t,
    V_d I ν A → V_d I μ Y → M.SuccessorOf μ ν → V_d I δ X → M.IsLimitOrdinal δ →
    M.mem ω δ → M.mem κ δ → Ep_source_d hZF ω κ K X S → Smem_d I c Y R →
    Tt_realized_d I ω c Y R n s δ U D t →
    (Ee_elastic_d q t ↔ Sc_inaccessible_d ω Y δ ∧ ∃ b Q w, Smem_d I b A Q ∧ Tm_minus_d I ω D t w ∧
      Tt_realized_d I ω b A Q n s δ U D w ∧ ∀ τ, M.mem τ δ → Ee_step_d hZF ω κ δ n s b X S w τ)

def ee_read_m {d} (ω κ n U D g h i e : Term d) : Formula 1 d := set[d] ⟪∀ ν μ A Y X c R δ K S s t,
  ⌜v_m kpair_convention_l⌝ₚ(ν, A) → ⌜v_m kpair_convention_l⌝ₚ(μ, Y) →
  ⌜Formula.isSuccessor⌝ₚ(μ, ν) → ⌜v_m kpair_convention_l⌝ₚ(δ, X) → ⌜Formula.isLimitOrdinal⌝ₚ(δ) →
  ⌜ω⌝ₛ ∈ δ → ⌜κ⌝ₛ ∈ δ → ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, K, X, S) →
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, t) →
  (⌜ee_elastic_m⌝ₚ(⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ, t) ↔ ⌜sc_inaccessible_raw_m⌝ₚ(⌜ω⌝ₛ, Y, δ) ∧
    (∃ b Q w, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(b, A, Q) ∧ ⌜tm_minus_m⌝ₚ(⌜ω⌝ₛ, ⌜D⌝ₛ, t, w) ∧
      ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, b, A, Q, ⌜n⌝ₛ, s, δ, ⌜U⌝ₛ, ⌜D⌝ₛ, w) ∧
      (∀ τ ∈ δ, ⌜ee_step0_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, δ, ⌜n⌝ₛ, s, b, X, S, w, τ))))⟫
derive_free_closed ee_read_m

theorem ee_read_sat_l {d} (ρ : Env M d) (ω κ n U D g h i e : Term d) :
    Formula.satisfies ρ (ee_read_m ω κ n U D g h i e) ↔
      Ee_read_d hZF (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ)
        ⟨g.eval ρ, h.eval ρ, i.eval ρ, e.eval ρ⟩ := by
  simp only [ee_read_m, Ee_read_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    v_sat_l I hZF.1, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff, ep_source_sat_l hZF, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF),
    Formula.satisfies_iff_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, ee_elastic_sat_l, sc_inaccessible_raw_sat_l, tm_minus_sat_l I hZF.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine forall_congr' fun ν => forall_congr' fun μ => forall_congr' fun A => forall_congr' fun Y =>
    forall_congr' fun X => forall_congr' fun c => forall_congr' fun R => forall_congr' fun δ =>
    forall_congr' fun K => forall_congr' fun S => forall_congr' fun s => forall_congr' fun t => ?_
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun source =>
    forall_congr' fun _ => forall_congr' fun _ => ?_
  refine iff_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun b => exists_congr fun Q => exists_congr fun w =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun τ => forall_congr' fun _ => ?_)))))
  let θ := ((((((((((((((((ρ.push ν).push μ).push A).push Y).push X).push c).push R).push δ).push K).push S).push s).push t).push b).push Q).push w).push τ)
  let v (a : Term d) := a.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  simpa only [θ, v, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
    ee_step0_sat_l hZF θ (v ω) (v κ) Term.newest.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken (v n)
      Term.newest.weaken.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken
      Term.newest.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
      Term.newest.weaken.weaken.weaken.weaken.weaken.weaken Term.newest.weaken .newest
      (by simpa only [θ, v, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using source)

end YesMetaZFC.SetTheory.LargeCardinal
