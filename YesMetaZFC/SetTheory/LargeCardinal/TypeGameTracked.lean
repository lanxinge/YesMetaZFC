import YesMetaZFC.SetTheory.LargeCardinal.TypeGameLevel
import YesMetaZFC.Model.Forcing.Internal.Ground.Arithmetic

/-! # 已捕获请求的实际有界高度谓词

谓词只读取递归图、枚举图和旧实现关系的像。它是扩张内部的原公式，
可对实际已捕获高度取最小元；反向读取同时恢复同一个地请求和两个旧前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

def Tg_tracked_d (ω H K enum R T G α : M.Domain) : Prop := ∃ n h i a k t g q,
  M.mem n ω ∧ Rd_entry_d n h H ∧ Rd_entry_d h i K ∧ Rd_entry_d i a enum ∧
  Rd_quad_d q a k t g ∧ Rd_entry_d q α R ∧ M.IsRestrictionOf I t T k ∧ M.IsRestrictionOf I g G k

def tg_tracked_m {d} (ω H K enum R T G α : Term d) : Formula 1 d := set[d] ⟪∃ n h i a k t g q,
  n ∈ ⌜ω⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(n, h, ⌜H⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(h, i, ⌜K⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(i, a, ⌜enum⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(q, a, k, t, g) ∧ ⌜rd_entry0_m⌝ₚ(q, ⌜α⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(t, ⌜T⌝ₛ, k) ∧ ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(g, ⌜G⌝ₛ, k)⟫
derive_free_closed tg_tracked_m

theorem tg_tracked_sat_l {d} (ρ : Env M d) (ω H K enum R T G α : Term d) :
    Formula.satisfies ρ (tg_tracked_m ω H K enum R T G α) ↔ Tg_tracked_d hM
      (ω.eval ρ) (H.eval ρ) (K.eval ρ) (enum.eval ρ) (R.eval ρ) (T.eval ρ) (G.eval ρ) (α.eval ρ) := by
  simp only [tg_tracked_m, Tg_tracked_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hM.1, rd_quad_sat_l hM.1,
    Formula.satisfies_isRestriction_iff I, Definitional.Term.eval_weaken]; rfl

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

omit hi in
theorem rd_quad_image_l {q a k t g : M.Domain} (code : Rd_quad_d q a k t g) :
    Rd_quad_d (e q) (e a) (e k) (e t) (e g) := by
  obtain ⟨v, vg, w, kw, aw⟩ := code
  exact ⟨e v, image_kpair_l e he vg, e w, image_kpair_l e he kw, image_kpair_l e he aw⟩

theorem Tg_level_table_d.track_l {p : Tg_params_d M.Domain} {X Z R n h a k t g α : M.Domain}
    {H K enum T G i : N.Domain} (table : Tg_level_table_d hM p X Z R)
    (hn : M.mem n p.ω) (nh : Rd_entry_d (e n) (e h) H) (ki : Rd_entry_d (e h) i K) (ia : Rd_entry_d i (e a) enum)
    (key : Tg_level_key_d hM p X Z a k t g α) (rt : N.IsRestrictionOf J (e t) T (e k)) (rg : N.IsRestrictionOf J (e g) G (e k)) :
    Tg_tracked_d hN (e p.ω) H K enum (e R) T G (e α) := by
  obtain ⟨q, code⟩ := rd_quad_exists_l (ZF.modelsKP hM) a k t g
  exact ⟨e n, e h, i, e a, e k, e t, e g, e q, (image_member_l e hi he).mpr hn, nh, ki, ia,
    rd_quad_image_l e he code, (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 q α R).mp
      ((table.2 q α).mpr ⟨a, k, t, g, code, key⟩), rt, rg⟩

omit hi in
theorem Tg_level_table_d.read_tracked_l {p : Tg_params_d M.Domain} {X Z R F : M.Domain}
    {H K enum T G α : N.Domain} (table : Tg_level_table_d hM p X Z R) (hf : Fn0_d (e p.ω) (e F) H)
    (tracked : Tg_tracked_d hN (e p.ω) H K enum (e R) T G α) :
    ∃ n h a k t g β, ∃ i : N.Domain, e β = α ∧ M.mem n p.ω ∧ Rd_entry_d (e n) (e h) H ∧
      Rd_entry_d (e h) i K ∧ Rd_entry_d i (e a) enum ∧ Tg_level_key_d hM p X Z a k t g β ∧
      N.IsRestrictionOf J (e t) T (e k) ∧ N.IsRestrictionOf J (e g) G (e k) := by
  obtain ⟨n, h, i, a, k, t, g, q, hn, nh, ki, ia, code, ent, rt, rg⟩ := tracked
  obtain ⟨n₀, hn₀, en⟩ := (he p.ω n).mp hn; subst n
  obtain ⟨h₀, _, eh⟩ := (he F h).mp (hf.bound_l nh).2; subst h
  obtain ⟨q₀, β, ent₀, eq, eβ⟩ := (image_entries_l e he table.1 q α).mp ent; subst q α
  obtain ⟨a₀, k₀, t₀, g₀, code₀, key⟩ := (table.2 q₀ β).mp ent₀
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (rd_quad_image_l e he code₀).unique_l code
  exact ⟨n₀, h₀, a₀, k₀, t₀, g₀, β, i, rfl, hn₀, nh, ki, ia, key, rt, rg⟩

omit hi he in
/-- 同一严格下降在扩张内部的最小高度上给出矛盾；不额外使用依赖选择。 -/
theorem tg_tracked_min_l {ω H K enum R T G α : M.Domain} (hα : M.IsOrdinal α)
    (initial : Tg_tracked_d hM ω H K enum R T G α) :
    ∃ β, M.IsOrdinal β ∧ Tg_tracked_d hM ω H K enum R T G β ∧
      ∀ γ, M.mem γ β → ¬ Tg_tracked_d hM ω H K enum R T G γ := by
  let ρ : Env M 7 := ⟨fun i => [ω, H, K, enum, R, T, G].get i, fun _ => ω⟩
  let φ : UnarySchema 7 := { body := tg_tracked_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) .newest }
  have sat β : φ.denote ρ β ↔ Tg_tracked_d hM ω H K enum R T G β := tg_tracked_sat_l hM ..
  obtain ⟨β, hβ, state, least⟩ := ZF.ordinal_min_l hM φ ρ hα ((sat α).mpr initial)
  exact ⟨β, hβ, (sat β).mp state, fun γ hγ h => least γ hγ ((sat γ).mpr h)⟩

end YesMetaZFC.SetTheory.LargeCardinal
