import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticLanguageSyntax
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple
import YesMetaZFC.Model.SetTheory.Internal.SourceAlgebra

/-! # 在任何对局出现之前固定弹性查询表

索引为模型自己的 (κ,n)，不是宿主自然数。集合内选择只执行一次，
结果是 Vδ 中数据之间的实际函数图；非极限 κ 的行取空集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ee_packet_d (hZF : M.Models ZF) (ω κ n r : M.Domain) : Prop :=
  ∃ B U D g h i e p, Rd_quad_d r B U D p ∧ Rd_quad_d p g h i e ∧
    Ee_language_d hZF ω κ n B U D ⟨g, h, i, e⟩

def ee_packet_m {d} (ω κ n r : Term d) : Formula 1 d := set[d] ⟪∃ B U D g h i e p,
  ⌜rd_quad_m⌝ₚ(⌜r⌝ₛ, B, U, D, p) ∧ ⌜rd_quad_m⌝ₚ(p, g, h, i, e) ∧
  ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜n⌝ₛ, B, U, D, g, h, i, e)⟫
derive_free_closed ee_packet_m

theorem ee_packet_sat_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (ω κ n r : Term d) :
    Formula.satisfies ρ (ee_packet_m ω κ n r) ↔
      Ee_packet_d (ZFC.models_zf_l hZFC) (ω.eval ρ) (κ.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [ee_packet_m, Ee_packet_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_quad_sat_l hZFC.1, ee_language_sat_l hZFC, Definitional.Term.eval_weaken]
  rfl

theorem sc_quad_l {X a b c d : M.Domain} (h : Sc_algebra_d X)
    (ha : M.mem a X) (hb : M.mem b X) (hc : M.mem c X) (hd : M.mem d X) :
    ∃ r, M.mem r X ∧ Rd_quad_d r a b c d := by
  obtain ⟨p, hp, cp⟩ := h.kpair_l hc hd
  obtain ⟨q, hq, cq⟩ := h.kpair_l hb hp
  obtain ⟨r, hr, cr⟩ := h.kpair_l ha hq
  exact ⟨r, hr, p, cp, q, cq, cr⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ee_packet_exists_l {ω δ X κ n : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (hX : V_d I δ X) (hk : M.mem κ δ) (hκ : M.IsLimitOrdinal κ) (hn : M.mem n ω) :
    ∃ r, M.mem r X ∧ Ee_packet_d hZF ω κ n r := by
  obtain ⟨B, U, D, q, language⟩ := ee_definition_l hZF hω hn hκ
  have algebra := sc_v_algebra_l hZFC hδ hX
  have trans := ZF.v_transitive_l I hZF hX
  have hB := ZF.v_mem_l I hZF language.rank hX hk
  have hU := tt_constants_rank_l hZF hX hδ hk language.rank language.constants
  have hD := language.pool.rank_mem_l hZF hω hX hδ (ZF.v_ordinal_mem_l I hZF hX hwδ) hn hU
  obtain ⟨p, hp, cp⟩ := sc_quad_l algebra (trans D hD q.largest language.largest_mem)
    (trans D hD q.domain language.domain_mem) (trans D hD q.inaccessible language.inaccessible_mem)
    (trans D hD q.stretch language.stretch_mem)
  obtain ⟨r, hr, cr⟩ := sc_quad_l algebra hB hU hD hp
  exact ⟨r, hr, B, U, D, q.largest, q.domain, q.inaccessible, q.stretch, p, cr, cp, language⟩

def Ee_catalog_d (ω δ X P Γ : M.Domain) : Prop := M.IsCartesianProduct I P δ ω ∧ Fn0_d P X Γ ∧
  ∀ κ n x r, M.mem κ δ → M.mem n ω → M.IsLimitOrdinal κ → KPair_d M x κ n →
    Rd_entry_d x r Γ → Ee_packet_d hZF ω κ n r

/-- 原公式的全定义关系在模型内统一化；表和每个键值对都实际存在。 -/
theorem ee_catalog_l {ω δ X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (hX : V_d I δ X) :
    ∃ P Γ, Ee_catalog_d hZFC ω δ X P Γ ∧ M.MemberSubset Γ X := by
  classical
  obtain ⟨P, product⟩ := ZF.exists_cartesianProduct hZF I δ ω
  obtain ⟨e, he, heω⟩ := hω.1.1
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push e
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ κ n,
    ⌜kpair0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ, κ, n) ∧
    ((⌜Formula.isLimitOrdinal⌝ₚ(κ) ∧ ⌜ee_packet_m⌝ₚ(⌜(.bound 3 : Term 4)⌝ₛ, κ, n, ⌜(.newest : Term 4)⌝ₛ)) ∨
      (¬ ⌜Formula.isLimitOrdinal⌝ₚ(κ) ∧ ⌜(.newest : Term 4)⌝ₛ = ⌜(.bound 2 : Term 4)⌝ₛ))⟫ }
  have sat x r : φ.denote ρ x r ↔ ∃ κ n, KPair_d M x κ n ∧
      ((M.IsLimitOrdinal κ ∧ Ee_packet_d hZF ω κ n r) ∨ (¬ M.IsLimitOrdinal κ ∧ r = e)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_isLimitOrdinal_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, kpair0_sat_l hZF.1, ee_packet_sat_l hZFC,
      Definitional.Term.eval_weaken]
    rfl
  have heX := ZF.v_transitive_l I hZF hX ω (ZF.v_ordinal_mem_l I hZF hX hwδ) e heω
  obtain ⟨Γ, fn, all⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := P) (Y := X) (fun x hx => by
    obtain ⟨κ, hk, n, hn, code⟩ := (product x).mp hx
    by_cases limit : M.IsLimitOrdinal κ
    · obtain ⟨r, hr, packet⟩ := ee_packet_exists_l hZFC hω hδ hwδ hX hk limit hn
      exact ⟨r, hr, (sat x r).mpr ⟨κ, n, code, Or.inl ⟨limit, packet⟩⟩⟩
    · exact ⟨e, heX, (sat x e).mpr ⟨κ, n, code, Or.inr ⟨limit, rfl⟩⟩⟩)
  refine ⟨P, Γ, ⟨product, fn0_of_function_l (ZF.modelsKP hZF) fn, fun κ n x r _ _ limit code entry => ?_⟩, ?_⟩
  · obtain ⟨κ', n', code', good⟩ := (sat x r).mp (all x r entry)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M code' code
    exact good.elim And.right (fun h => (h.1 limit).elim)
  · intro p hp
    obtain ⟨x, r, pair⟩ := fn.1.1 p hp
    have entry := (show M.PairMember I x r Γ from ⟨p, pair, hp⟩)
    obtain ⟨κ, hk, n, hn, key⟩ := (product x).mp (fn.input_mem_of_pairMember entry)
    have algebra := sc_v_algebra_l hZFC hδ hX
    have hnX := ZF.v_transitive_l I hZF hX ω (ZF.v_ordinal_mem_l I hZF hX hwδ) n hn
    obtain ⟨x', hx', key'⟩ := algebra.kpair_l (ZF.v_ordinal_mem_l I hZF hX hk) hnX
    have eq := kpair_unique_l M hZF.1 key' key
    obtain ⟨p', hp', pair'⟩ := algebra.kpair_l (eq ▸ hx') (fn.output_mem_of_pairMember entry)
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'

end YesMetaZFC.SetTheory.LargeCardinal
