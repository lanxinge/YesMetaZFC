import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericTarget
import YesMetaZFC.Model.Forcing.Internal.Forcing.Definability

/-! # 地模型稠密集与真实泛型性调用

有限条件的延长定理给出稠密性；原公式给出地模型中的分离集合。
直接使用已有泛型滤子的 meets，不假设泛型枚举具有额外的请求公平性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
open Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

theorem tg_dense_hit_defined_l (hZF : M.Models ZF) (p : Tg_params_d M.Domain) (ℓ s t k N β g a₀ b₀ E : M.Domain) :
    Defined_d M (Tg_dense_hit_d hZF p ℓ s t k N β g a₀ b₀ E) := by
  let ρ : Env M 22 := ⟨fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q,
    ℓ, s, t, k, N, β, g, a₀, b₀, E].get i, fun _ => p.ω⟩
  let a : Tg_params_d (Term 23) := ⟨.bound 1, .bound 2, .bound 3, .bound 4, .bound 5, .bound 6,
    .bound 7, .bound 8, .bound 9, .bound 10, .bound 11, .bound 12⟩
  let φ : UnarySchema 22 := {
    body := tg_dense_hit_m a (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
      (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22) .newest
    freeClosed := by
      simp -implicitDefEqProofs [tg_dense_hit_m, Definitional.Formula.FreeClosed, a]
      apply tg_generic_target_closed_l <;>
        simp -implicitDefEqProofs [Tg_params_d.closed_l, Tg_params_d.map_l] }
  refine ⟨22, φ, ρ, fun q => ?_⟩
  exact tg_dense_hit_sat_l hZF (ρ.push q) a (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
    (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22) .newest

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.generic_meet_l {p : Tg_params_d M.Domain}
    {X ℓ a₀ ℓ₀ t₀ κ₀ u₀ b₀ j k N τ B U D w η Y c R r g β s t g' x F Q E : M.Domain}
    {q₀ : Tg_reply_queries_d M} {G : M.Domain → Prop}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (hℓ : M.mem ℓ p.ω)
    (oldMove : Tg_aux_data_d a₀ ℓ₀ t₀ κ₀ u₀) (oldAnswer : KPair_d M b₀ τ w)
    (ft₀ : Fn0_d j p.ω t₀) (hk : M.SuccessorOf k j) (hN : M.SuccessorOf N k)
    (ft : Fn0_d k p.ω t) (cut : M.IsRestrictionOf I t₀ t j)
    (oldLanguage : Tg_reply_language_d hZF p.ω p.e k N τ B U D q₀)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I p.ω c Y R N r p.δ U D w)
    (rS : Rd_entry_d p.e p.S r) (last : Rd_entry_d k β r) (set : Sg_set_d I p.e k r g)
    (bound : Tg_bound_d I p.δ p.S β) (height : Tg_height_d β η)
    (node : Tg_node_d I k p.S s t g') (extend : ∀ a, M.mem a g' ↔ M.mem a g ∨ a = x)
    (hτ : M.mem τ p.δ) (hs : M.mem s X) (ht : M.mem t X) (space : Fseq_space_d I p.ω X F)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F G) (hE : M.mem E p.ω) :
    ∃ q, G q ∧ Tg_dense_hit_d hZF p ℓ s t k N β g' a₀ b₀ E q := by
  obtain ⟨f, hf⟩ := generic.inhabited
  apply generic_pick_l hZF generic (tg_dense_hit_defined_l hZF p ℓ s t k N β g' a₀ b₀ E) hf
  intro q hq
  obtain ⟨κ, C, a, u, μ, A, d, H, m, V, P, r', i, q', hκ, hC, ha, move, hμ, hA, lower,
    hm, constants, full, first, last, labels, hq', sub, hEi, hi, ia, before, legal⟩ :=
    setup.generic_dense_l hZFC hd hℓ oldMove oldAnswer ft₀ hk hN ft cut oldLanguage hY model type
      rS last set bound height node extend hτ hs ht space hq.1 hE
  exact ⟨q', subset_below_l hZF order hq.1 hq' sub,
    κ, C, a, u, i, ⟨hκ, hC, move, ⟨μ, A, d, H, m, V, P, r', hμ, hA, lower, hm, constants, full, first, last, labels⟩, legal⟩,
    hEi, hi, ia, before⟩

end YesMetaZFC.SetTheory.LargeCardinal
