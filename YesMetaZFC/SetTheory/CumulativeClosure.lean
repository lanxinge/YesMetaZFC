import YesMetaZFC.SetTheory.Cumulative
import YesMetaZFC.SetTheory.Kuratowski
import YesMetaZFC.SetTheory.MembershipInduction
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Construction

/-! # 极限累积层中的实际幂集封闭

先读取 x 所在的较早层，再提高一次指标，便能把 P(x) 的全部成员统一放入一层。
这一封闭性无需不可达性、正则性或选择公理。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ZF.v_ordinal_subset_l (hZF : M.Models ZF) {α V} (hV : V_d I α V) : M.MemberSubset α V := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => α⟩
  let φ : UnarySchema 0 := { body := .imp (Formula.isOrdinal .newest) (.forallE
    (.imp (v_m 𝒞 (.bound 1) .newest) (Formula.subset (.bound 1) .newest))) }
  have sat a : φ.denote ρ a ↔ (M.IsOrdinal a → ∀ W, V_d I a W → M.MemberSubset a W) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_isOrdinal_iff,
      Formula.satisfies_forall_iff, v_sat_l I hZF.1, Formula.satisfies_subset_iff]
    rfl
  apply (sat α).mp ((mem_ind_l M hZF I) φ ρ ?_ α) (v_ordinal_l I hV) V hV
  intro a ih
  apply (sat a).mpr
  intro ha W hW b hb
  obtain ⟨Z, hZ⟩ := v_exists_l I hZF (ha.mem hb)
  exact (v_unfold_l I hZF hW b).mpr ⟨b, Z, hb, hZ, (sat b).mp (ih b hb) (ha.mem hb) Z hZ⟩

theorem ZF.v_ordinal_mem_l (hZF : M.Models ZF) {α β V} (hV : V_d I β V) (hαβ : M.mem α β) : M.mem α V := by
  obtain ⟨W, hW⟩ := v_exists_l I hZF ((v_ordinal_l I hV).mem hαβ)
  exact (v_unfold_l I hZF hV α).mpr ⟨α, W, hαβ, hW, v_ordinal_subset_l I hZF hW⟩

theorem ZF.v_power_mem_l (hZF : M.Models ZF) {δ V x P} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hx : M.mem x V) (hP : M.IsPowerSetOf P x) : M.mem P V := by
  obtain ⟨β, W, hβ, hW, hxW⟩ := (v_unfold_l I hZF hV x).mp hx
  obtain ⟨γ, hγ, hβγ⟩ := hδ.2.2 β hβ
  obtain ⟨Z, hZ⟩ := v_exists_l I hZF (hδ.1.mem hγ)
  exact (v_unfold_l I hZF hV P).mpr ⟨γ, Z, hγ, hZ, fun s hs =>
    (v_unfold_l I hZF hZ s).mpr ⟨β, W, hβγ, hW, fun y hy => hxW y ((hP s).mp hs y hy)⟩⟩

/-- 两个已在秩层中的集合，其成员统一落在同一个更早秩层。 -/
theorem ZF.v_joint_bound_l (hZF : M.Models ZF) {δ V x y} (hV : V_d I δ V)
    (hx : M.mem x V) (hy : M.mem y V) : ∃ R, M.mem R V ∧ M.MemberSubset x R ∧ M.MemberSubset y R := by
  obtain ⟨α, P, hα, hP, hxP⟩ := (v_unfold_l I hZF hV x).mp hx
  obtain ⟨β, Q, hβ, hQ, hyQ⟩ := (v_unfold_l I hZF hV y).mp hy
  have mem {γ R} (hγ : M.mem γ δ) (hR : V_d I γ R) : M.mem R V :=
    (v_unfold_l I hZF hV R).mpr ⟨γ, R, hγ, hR, fun _ h => h⟩
  rcases (v_ordinal_l I hV).wellOrder.linear.compare α hα β hβ with he | he | he
  · exact ⟨Q, mem hβ hQ, fun z hz => ZF.v_mono_l I hZF hP hQ (fun t ht => (he t).mp ht) z (hxP z hz), hyQ⟩
  · exact ⟨Q, mem hβ hQ, fun z hz => ZF.v_mono_l I hZF hP hQ ((v_ordinal_l I hQ).transitive α he) z (hxP z hz), hyQ⟩
  · exact ⟨P, mem hα hP, hxP, fun z hz => ZF.v_mono_l I hZF hQ hP ((v_ordinal_l I hP).transitive β he) z (hyQ z hz)⟩

/-- 同一个内部集合统一容纳载体上的全部 Kuratowski 关系图。 -/
theorem ZF.v_relation_cover_l (hZF : M.Models ZF) {δ V Y} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V) : ∃ R, M.mem R V ∧ ∀ F,
      (∀ p, M.mem p F → ∃ a, M.mem a Y ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b) → M.mem F R := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF Y
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  obtain ⟨R, hR⟩ := ZF.exists_powerSet hZF Q
  have hPV := v_power_mem_l I hZF hV hδ hY hP
  have hQV := v_power_mem_l I hZF hV hδ hPV hQ
  have hRV := v_power_mem_l I hZF hV hδ hQV hR
  refine ⟨R, hRV, fun F hF => (hR F).mpr ?_⟩
  intro p hp
  obtain ⟨a, ha, b, hb, s, t, hs, ht, hp⟩ := hF p hp
  have hPs : M.mem s P := (hP s).mpr (fun x hx => (hs x).mp hx ▸ ha)
  have hPt : M.mem t P := (hP t).mpr (fun x hx => ((ht x).mp hx).elim (fun h => h ▸ ha) (fun h => h ▸ hb))
  exact (hQ p).mpr (fun x hx => ((hp x).mp hx).elim (fun h => h ▸ hPs) (fun h => h ▸ hPt))

theorem ZF.v_relation_mem_l (hZF : M.Models ZF) {δ V Y F} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V)
    (hF : ∀ p, M.mem p F → ∃ a, M.mem a Y ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b) : M.mem F V := by
  obtain ⟨R, hRV, hr⟩ := v_relation_cover_l I hZF hV hδ hY
  exact v_transitive_l I hZF hV R hRV F (hr F hF)

theorem ZF.v_relations_mem_l (hZF : M.Models ZF) {δ V Y T} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V)
    (hT : ∀ f, M.mem f T → ∀ p, M.mem p f → ∃ a, M.mem a Y ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b) : M.mem T V := by
  obtain ⟨R, hRV, hr⟩ := v_relation_cover_l I hZF hV hδ hY
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF R
  exact v_transitive_l I hZF hV P (v_power_mem_l I hZF hV hδ hRV hP) T ((hP T).mpr fun f hf => hr f (hT f hf))

theorem ZF.v_function_space_mem_l (hZF : M.Models ZF) {δ V D Y G} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V) (hD : M.MemberSubset D Y)
    (hG : M.IsFunctionSpace (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) G D Y) : M.mem G V := by
  apply v_relations_mem_l I hZF hV hδ hY
  intro f hf p hp
  have hf := (hG f).mp hf
  obtain ⟨a, b, hab⟩ := hf.1.1 p hp
  exact ⟨a, hD a (hf.input_mem_of_pairMember ⟨p, hab, hp⟩), b,
    hf.output_mem_of_pairMember ⟨p, hab, hp⟩, hab⟩

theorem ZF.v_subset_mem_l (hZF : M.Models ZF) {δ V A B} (hV : V_d I δ V)
    (hA : M.mem A V) (hB : M.MemberSubset B A) : M.mem B V := by
  obtain ⟨β, W, hβ, hW, sub⟩ := (v_unfold_l I hZF hV A).mp hA
  exact (v_unfold_l I hZF hV B).mpr ⟨β, W, hβ, hW, fun x hx => sub x (hB x hx)⟩

theorem ZF.v_product_mem_l (hZF : M.Models ZF) {δ V A B P} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hA : M.mem A V) (hB : M.mem B V)
    (hP : M.IsCartesianProduct (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) P A B) : M.mem P V := by
  obtain ⟨Y, hY, hAY, hBY⟩ := v_joint_bound_l I hZF hV hA hB
  exact v_relation_mem_l I hZF hV hδ hY fun p hp =>
    (hP p).mp hp |>.elim fun a ha => ha.2.elim fun b hb => ⟨a, hAY a ha.1, b, hBY b hb.1, hb.2⟩

theorem ZF.v_fseq_mem_l (hZF : M.Models ZF) {δ V ω A J} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hω : M.IsOmega ω) (hωV : M.mem ω V) (hA : M.mem A V)
    (hJ : Fseq_space_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω A J) : M.mem J V := by
  obtain ⟨Y, hY, hωY, hAY⟩ := v_joint_bound_l I hZF hV hωV hA
  apply v_relations_mem_l I hZF hV hδ hY
  intro f hf p hp
  obtain ⟨n, hn, fn⟩ := (hJ f).mp hf
  obtain ⟨a, b, code⟩ := fn.1.1 p hp
  exact ⟨a, hωY a (hω.transitive hZF n hn a (fn.input_mem_of_pairMember ⟨p, code, hp⟩)),
    b, hAY b (fn.output_mem_of_pairMember ⟨p, code, hp⟩), code⟩

theorem ZF.v_fibers_mem_l (hZF : M.Models ZF) {δ V R B T} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hR : M.mem R V) (hT : InnerModel.Rd_fun_d .fibers R B R T) : M.mem T V := by
  obtain ⟨β, Y, hβ, hy, hRY⟩ := (v_unfold_l I hZF hV R).mp hR
  have ht := v_transitive_l I hZF hy
  obtain ⟨P, hp⟩ := exists_powerSet hZF Y
  apply v_subset_mem_l I hZF hV (v_power_mem_l I hZF hV hδ (v_mem_l I hZF hy hV hβ) hp)
  intro t h
  obtain ⟨b, _, fiber⟩ := (hT t).mp h
  apply (hp t).mpr
  intro x hx
  obtain ⟨p, code, hpr⟩ := (fiber x).mp hx
  obtain ⟨s, hs, hxs⟩ := (kpair_union_l M code x).mpr (Or.inl rfl)
  exact ht s (ht p (hRY p hpr) s hs) x hxs

end YesMetaZFC.SetTheory
