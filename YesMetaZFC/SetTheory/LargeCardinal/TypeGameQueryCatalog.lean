import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryPacket

/-! # 节点和端点查询的实际统一表

每个合法键 (κ,k,s,t) 恰查询同一行；整个表在任何局面出现前取定。
表的无关键取空值，游戏读取则必须先验证原参数域和合法键条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_query_key_d (hZF : M.Models ZF) (ω δ x : M.Domain) : Prop :=
  ∃ κ k s t, Rd_quad_d x κ k s t ∧ M.mem κ δ ∧ Tg_query_request_d hZF ω κ k s t

def tg_query_key_m {d} (ω δ x : Term d) : Formula 1 d := set[d] ⟪∃ κ k s t,
  ⌜rd_quad_m⌝ₚ(⌜x⌝ₛ, κ, k, s, t) ∧ κ ∈ ⌜δ⌝ₛ ∧ ⌜tg_query_request_m⌝ₚ(⌜ω⌝ₛ, κ, k, s, t)⟫
derive_free_closed tg_query_key_m

theorem tg_query_key_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω δ x : Term d) :
    Formula.satisfies ρ (tg_query_key_m ω δ x) ↔ Tg_query_key_d hZF (ω.eval ρ) (δ.eval ρ) (x.eval ρ) := by
  simp only [tg_query_key_m, Tg_query_key_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_quad_sat_l hZF.1, tg_query_request_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_query_catalog_d (ω e δ X Γ : M.Domain) : Prop := Fn0_d X X Γ ∧
  ∀ κ k s t x c, Rd_quad_d x κ k s t → M.mem κ δ → Tg_query_request_d hZF ω κ k s t →
    Rd_entry_d x c Γ → Tg_query_packet_d hZF ω e κ k s t c

theorem tg_query_catalog_l {ω e δ X : M.Domain} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (hX : V_d I δ X) :
    ∃ Γ, Tg_query_catalog_d hZFC ω e δ X Γ ∧ M.MemberSubset Γ X := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push e).push δ
  let φ : BinarySchema 3 := { body := set[5] ⟪(∃ κ k s t,
    ⌜rd_quad_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, κ, k, s, t) ∧ κ ∈ ⌜(.bound 2 : Term 5)⌝ₛ ∧
    ⌜tg_query_request_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, κ, k, s, t) ∧
    ⌜tg_query_packet_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, κ, k, s, t, ⌜(.newest : Term 5)⌝ₛ)) ∨
    (¬ ⌜tg_query_key_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 1 : Term 5)⌝ₛ) ∧
      ⌜(.newest : Term 5)⌝ₛ = ⌜(.bound 3 : Term 5)⌝ₛ)⟫ }
  have sat x c : φ.denote ρ x c ↔
      (∃ κ k s t, Rd_quad_d x κ k s t ∧ M.mem κ δ ∧ Tg_query_request_d hZF ω κ k s t ∧
        Tg_query_packet_d hZF ω e κ k s t c) ∨ (¬ Tg_query_key_d hZF ω δ x ∧ c = e) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, rd_quad_sat_l hZF.1, tg_query_request_sat_l hZF,
      tg_query_packet_sat_l hZF, tg_query_key_sat_l hZF, Definitional.Term.eval_weaken]
    rfl
  have heω := num_mem_l hZF.1 hω (show Num_d 0 e from he)
  have heX := ZF.v_transitive_l I hZF hX ω (ZF.v_ordinal_mem_l I hZF hX hwδ) e heω
  obtain ⟨Γ, fn, all⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := X) (Y := X) (fun x _ => by
    by_cases key : Tg_query_key_d hZF ω δ x
    · obtain ⟨κ, k, s, t, code, hk, request⟩ := key
      obtain ⟨c, hc, packet⟩ := tg_query_packet_exists_l hZFC hω he hδ hwδ hX hk request
      exact ⟨c, hc, (sat x c).mpr (Or.inl ⟨κ, k, s, t, code, hk, request, packet⟩)⟩
    · exact ⟨e, heX, (sat x e).mpr (Or.inr ⟨key, rfl⟩)⟩)
  refine ⟨Γ, ⟨fn0_of_function_l (ZF.modelsKP hZF) fn, fun κ k s t x c code hk request entry => ?_⟩, ?_⟩
  · rcases (sat x c).mp (all x c entry) with ⟨κ', k', s', t', code', _, _, packet⟩ | invalid
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := code'.unique_l code
      exact packet
    · exact (invalid.1 ⟨κ, k, s, t, code, hk, request⟩).elim
  · intro p hp
    obtain ⟨x, c, pair⟩ := fn.1.1 p hp
    have entry : Rd_entry_d x c Γ := ⟨p, pair, hp⟩
    obtain ⟨p', hp', pair'⟩ := (sc_v_algebra_l hZFC hδ hX).kpair_l
      (fn.input_mem_of_pairMember entry) (fn.output_mem_of_pairMember entry)
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'

theorem Tg_query_catalog_d.get_l {ω e δ X Γ κ k s t : M.Domain} (table : Tg_query_catalog_d hZFC ω e δ X Γ)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (hX : V_d I δ X)
    (hk : M.mem κ δ) (request : Tg_query_request_d hZF ω κ k s t) :
    ∃ x c, Rd_quad_d x κ k s t ∧ Rd_entry_d x c Γ ∧ Tg_query_packet_d hZF ω e κ k s t c := by
  obtain ⟨limit, finite, B, U, rank, constants, hs, ht⟩ := request
  have trans := ZF.v_transitive_l I hZF hX
  have hU := tt_constants_rank_l hZF hX hδ hk rank constants
  obtain ⟨x, hx, code⟩ := sc_quad_l (sc_v_algebra_l hZFC hδ hX) (ZF.v_ordinal_mem_l I hZF hX hk)
    (trans ω (ZF.v_ordinal_mem_l I hZF hX hwδ) k finite) (trans U hU s hs) (trans U hU t ht)
  obtain ⟨c, _, entry⟩ := table.1.2.1 x hx
  exact ⟨x, c, code, entry, table.2 κ k s t x c code hk ⟨limit, finite, B, U, rank, constants, hs, ht⟩ entry⟩

end YesMetaZFC.SetTheory.LargeCardinal
