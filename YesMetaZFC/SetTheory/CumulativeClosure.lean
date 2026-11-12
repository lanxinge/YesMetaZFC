import YesMetaZFC.SetTheory.Cumulative
import YesMetaZFC.SetTheory.Kuratowski
import YesMetaZFC.SetTheory.MembershipInduction
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Construction
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 极限累积层中的实际幂集封闭

对给定实际秩历史直接比较层值并提高有限次指标，回收已有子集、幂集、关系图及图族。
这些闭包不需要模型公理、全局层级唯一性或额外幂集构造。
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

/-- 同一份实际历史中的每层方程；无需另造层级或比较两份递归。 -/
private theorem v_history_l {δ V : M.Domain} (hV : V_d I δ V) :
    ∃ F, M.IsDomainOf I δ F ∧
      (∀ α W, M.PairMember I α W F → ∀ x, M.mem x W ↔
        ∃ β, M.mem β α ∧ ∃ Y, M.PairMember I β Y F ∧ M.MemberSubset x Y) ∧ V_step_d I F V := by
  obtain ⟨F, hf, root⟩ := hV
  refine ⟨F, hf.1.2.2, ?_, root⟩
  intro α W hα x
  obtain ⟨G, rest, step⟩ := hf.2 α ((hf.1.2.2 α).mpr ⟨W, hα⟩) W hα
  exact (step x).trans ⟨fun ⟨β, Y, hβ, sub⟩ =>
    ⟨β, ((rest.2 β Y).mp hβ).1, Y, ((rest.2 β Y).mp hβ).2, sub⟩,
    fun ⟨β, hβ, Y, hy, sub⟩ => ⟨β, Y, (rest.2 β Y).mpr ⟨hβ, hy⟩, sub⟩⟩

/-- 固定 Kuratowski 秩历史内的最小反例只需有界分离；不重建递归层级。 -/
theorem KP.v_ordinal_subset_l (hKP : M.Models KP) {α V : M.Domain}
    (hV : V_d (InnerModel.kp_pair_l hKP) α V) : M.MemberSubset α V := by
  classical
  let J := InnerModel.kp_pair_l hKP
  obtain ⟨F, dom, step, root⟩ := v_history_l J hV
  have bound β W (hβW : M.PairMember J β W F) : M.mem W V :=
    (root W).mpr ⟨β, W, hβW, fun _ h => h⟩
  let ρ : Env M 2 := ⟨Fin.cases F (fun _ => V), fun _ => α⟩
  let φ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 2) (.conj (InnerModel.rd_entry0_m (.bound 1) .newest (.bound 2))
      (.neg (Formula.subset (.bound 1) .newest)))
    delta0 := .existsMem _ (.conj (InnerModel.rd_entry0_delta_l ..) (.neg (.atom ..))) }
  have read β : φ.toUnarySchema.denote ρ β ↔ ∃ W, M.mem W V ∧ M.PairMember J β W F ∧ ¬ M.MemberSubset β W := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      InnerModel.rd_entry0_sat_l hKP.1, Formula.satisfies_neg_iff, Formula.satisfies_subset_iff]; rfl
  obtain ⟨B, sep⟩ := KP.separation_exists_d hKP φ ρ α
  have bad β := (sep β).trans (and_congr_right fun _ => read β)
  have empty : ¬ ∃ β, M.mem β B := by
    intro nonempty
    obtain ⟨β, hβ, minimal⟩ := KP.mem_minimal_exists_d hKP nonempty
    obtain ⟨hβα, W, _, hβW, fail⟩ := (bad β).mp hβ
    apply fail
    intro γ hγβ
    have hγα := (v_ordinal_l J hV).transitive β hβα γ hγβ
    obtain ⟨U, hγU⟩ := (dom γ).mp hγα
    have sub : M.MemberSubset γ U := by
      apply Classical.byContradiction
      intro no
      exact minimal γ ((bad γ).mpr ⟨hγα, U, bound γ U hγU, hγU, no⟩) hγβ
    exact (step β W hβW γ).mpr ⟨γ, hγβ, U, hγU, sub⟩
  intro β hβ
  obtain ⟨W, hβW⟩ := (dom β).mp hβ
  apply (root β).mpr ⟨β, W, hβW, ?_⟩
  apply Classical.byContradiction
  intro no
  exact empty ⟨β, (bad β).mpr ⟨hβ, W, bound β W hβW, hβW, no⟩⟩

/-- 已有层值对其成员的实际子集封闭，不需要任何模型公理。 -/
theorem v_subset_mem_l {δ V A B : M.Domain} (hV : V_d I δ V)
    (hA : M.mem A V) (sub : M.MemberSubset B A) : M.mem B V := by
  obtain ⟨F, _, root⟩ := hV
  obtain ⟨α, W, hα, aw⟩ := (root A).mp hA
  exact (root B).mpr ⟨α, W, hα, fun x hx => aw x (sub x hx)⟩

/-- 秩层已包含其成员的全部实际子集；一次 KP 分离即可构造完整幂集。 -/
theorem v_power_exists_l (hKP : M.Models KP) {δ V x : M.Domain}
    (hV : V_d I δ V) (hx : M.mem x V) : ∃ P, M.IsPowerSetOf P x := by
  let φ : Delta0UnarySchema 1 := { body := Formula.subset .newest (.bound 1), delta0 := .atom .. }
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  obtain ⟨P, spec⟩ := KP.separation_exists_d hKP φ ρ V
  have read A : Formula.satisfies (ρ.push A) φ.body ↔ M.MemberSubset A x := Formula.satisfies_subset_iff ..
  exact ⟨P, fun A => (spec A).trans ((and_congr_right fun _ => read A).trans
    ⟨And.right, fun sub => ⟨v_subset_mem_l I hV hx sub, sub⟩⟩)⟩

/-- 给定幂集的全部成员落在下一历史层中，故幂集本身仍属于极限层。 -/
theorem v_power_mem_l {δ V x P : M.Domain} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hx : M.mem x V) (hP : M.IsPowerSetOf P x) : M.mem P V := by
  obtain ⟨F, dom, step, root⟩ := v_history_l I hV
  obtain ⟨β, W, hβW, xw⟩ := (root x).mp hx
  obtain ⟨γ, hγ, hβγ⟩ := hδ.2.2 β ((dom β).mpr ⟨W, hβW⟩)
  obtain ⟨Q, hγQ⟩ := (dom γ).mp hγ
  exact (root P).mpr ⟨γ, Q, hγQ, fun s hs => (step γ Q hγQ s).mpr
    ⟨β, hβγ, W, hβW, fun y hy => xw y ((hP s).mp hs y hy)⟩⟩

/-- 两个坐标界直接在同一历史中比较，不调用层级唯一性。 -/
theorem v_joint_bound_l {δ V x y : M.Domain} (hV : V_d I δ V)
    (hx : M.mem x V) (hy : M.mem y V) : ∃ R, M.mem R V ∧ M.MemberSubset x R ∧ M.MemberSubset y R := by
  obtain ⟨F, dom, step, root⟩ := v_history_l I hV
  obtain ⟨α, P, hαP, xp⟩ := (root x).mp hx
  obtain ⟨β, Q, hβQ, yq⟩ := (root y).mp hy
  have member γ R (hr : M.PairMember I γ R F) : M.mem R V :=
    (root R).mpr ⟨γ, R, hr, fun _ h => h⟩
  have mono α β P Q (hp : M.PairMember I α P F) (hq : M.PairMember I β Q F)
      (ab : M.MemberSubset α β) : M.MemberSubset P Q := by
    intro z hz
    obtain ⟨γ, hγ, R, hr, sub⟩ := (step α P hp z).mp hz
    exact (step β Q hq z).mpr ⟨γ, ab γ hγ, R, hr, sub⟩
  rcases (v_ordinal_l I hV).wellOrder.linear.compare α ((dom α).mpr ⟨P, hαP⟩)
    β ((dom β).mpr ⟨Q, hβQ⟩) with eq | lt | gt
  · exact ⟨Q, member β Q hβQ, fun z hz => mono α β P Q hαP hβQ (fun t ht => (eq t).mp ht) z (xp z hz), yq⟩
  · exact ⟨Q, member β Q hβQ, fun z hz => mono α β P Q hαP hβQ
      ((v_ordinal_l I hV).mem ((dom β).mpr ⟨Q, hβQ⟩) |>.transitive α lt) z (xp z hz), yq⟩
  · exact ⟨P, member α P hαP, xp, fun z hz => mono β α Q P hβQ hαP
      ((v_ordinal_l I hV).mem ((dom α).mpr ⟨P, hαP⟩) |>.transitive β gt) z (yq z hz)⟩

-- 单点、无序对、有序对和关系图依次放进已有历史层；每一步都保留原见证。
private theorem v_relation_data_l {δ V Y : M.Domain} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V) :
    ∃ R, M.mem R V ∧ M.MemberSubset R V ∧ ∀ F,
      (∀ p, M.mem p F → ∃ a, M.mem a Y ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b) → M.mem F R := by
  obtain ⟨G, dom, step, root⟩ := v_history_l I hV
  obtain ⟨β, P, hβP, yp⟩ := (root Y).mp hY
  obtain ⟨γ, hγ, hβγ⟩ := hδ.2.2 β ((dom β).mpr ⟨P, hβP⟩)
  obtain ⟨η, hη, hγη⟩ := hδ.2.2 γ hγ
  obtain ⟨ε, hε, hηε⟩ := hδ.2.2 η hη
  obtain ⟨Q, hγQ⟩ := (dom γ).mp hγ
  obtain ⟨T, hηT⟩ := (dom η).mp hη
  obtain ⟨R, hεR⟩ := (dom ε).mp hε
  refine ⟨R, (root R).mpr ⟨ε, R, hεR, fun _ h => h⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨α, _, W, hw, sub⟩ := (step ε R hεR x).mp hx
    exact (root x).mpr ⟨α, W, hw, sub⟩
  · intro F bound
    refine (step ε R hεR F).mpr ⟨η, hηε, T, hηT, fun p hp => ?_⟩
    obtain ⟨a, ha, b, hb, s, t, hs, ht, pair⟩ := bound p hp
    have hsQ := (step γ Q hγQ s).mpr ⟨β, hβγ, P, hβP, fun x hx => (hs x).mp hx ▸ yp a ha⟩
    have htQ := (step γ Q hγQ t).mpr ⟨β, hβγ, P, hβP,
      fun x hx => ((ht x).mp hx).elim (fun eq => eq ▸ yp a ha) (fun eq => eq ▸ yp b hb)⟩
    exact (step η T hηT p).mpr ⟨γ, hγη, Q, hγQ,
      fun x hx => ((pair x).mp hx).elim (fun eq => eq ▸ hsQ) (fun eq => eq ▸ htQ)⟩

/-- 同一历史层统一容纳给定载体上的全部实际 Kuratowski 关系图。 -/
theorem v_relation_cover_l {δ V Y : M.Domain} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V) : ∃ R, M.mem R V ∧ ∀ F,
      (∀ p, M.mem p F → ∃ a, M.mem a Y ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b) → M.mem F R := by
  obtain ⟨R, hr, _, cover⟩ := v_relation_data_l I hV hδ hY
  exact ⟨R, hr, cover⟩

theorem v_relation_mem_l {δ V Y F : M.Domain} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V)
    (bound : ∀ p, M.mem p F → ∃ a, M.mem a Y ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b) : M.mem F V := by
  obtain ⟨R, _, sub, cover⟩ := v_relation_data_l I hV hδ hY
  exact sub F (cover F bound)

theorem v_relations_mem_l {δ V Y T : M.Domain} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V)
    (bound : ∀ f, M.mem f T → ∀ p, M.mem p f → ∃ a, M.mem a Y ∧ ∃ b, M.mem b Y ∧ KPair_d M p a b) : M.mem T V := by
  obtain ⟨R, hr, _, cover⟩ := v_relation_data_l I hV hδ hY
  exact v_subset_mem_l I hV hr (fun f hf => cover f (bound f hf))

/-- 已有极限历史统一界定全部函数图；KP 分离构造实际函数空间。 -/
theorem v_fspace_exists_l (hKP : M.Models KP) {δ V D A : M.Domain}
    (hV : V_d I δ V) (hδ : M.IsLimitOrdinal δ) (hD : M.mem D V) (hA : M.mem A V) :
    ∃ G, M.mem G V ∧ ∀ f, M.mem f G ↔ InnerModel.Fn0_d D A f := by
  obtain ⟨Y, hY, dy, ay⟩ := v_joint_bound_l I hV hD hA
  obtain ⟨R, hR, cover⟩ := v_relation_cover_l I hV hδ hY
  let ρ : Env M 2 := ⟨Fin.cases A (fun _ => D), fun _ => D⟩
  let φ : Delta0UnarySchema 2 := {
    body := InnerModel.fn0_m (.bound 2) (.bound 1) .newest
    delta0 := InnerModel.fn0_delta_l .. }
  have read f : φ.toUnarySchema.denote ρ f ↔ InnerModel.Fn0_d D A f := InnerModel.fn0_sat_l hKP.1 ..
  obtain ⟨G, spec⟩ := KP.separation_exists_d hKP φ ρ R
  refine ⟨G, v_subset_mem_l I hV hR (fun f hf => ((spec f).mp hf).1), fun f =>
    (spec f).trans ((and_congr_right fun _ => read f).trans ⟨And.right, fun hf => ⟨?_, hf⟩⟩)⟩
  exact cover f (fun p hp => (hf.1 p hp).elim fun a ha => ha.2.elim fun b hb =>
    ⟨a, dy a ha.1, b, ay b hb.1, hb.2⟩)

theorem ZF.v_function_space_mem_l (hZF : M.Models ZF) {δ V D Y G} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hY : M.mem Y V) (hD : M.MemberSubset D Y)
    (hG : M.IsFunctionSpace (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) G D Y) : M.mem G V := by
  apply v_relations_mem_l I hV hδ hY
  intro f hf p hp
  have hf := (hG f).mp hf
  obtain ⟨a, b, hab⟩ := hf.1.1 p hp
  exact ⟨a, hD a (hf.input_mem_of_pairMember ⟨p, hab, hp⟩), b,
    hf.output_mem_of_pairMember ⟨p, hab, hp⟩, hab⟩

theorem ZF.v_product_mem_l (hZF : M.Models ZF) {δ V A B P} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hA : M.mem A V) (hB : M.mem B V)
    (hP : M.IsCartesianProduct (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) P A B) : M.mem P V := by
  obtain ⟨Y, hY, hAY, hBY⟩ := v_joint_bound_l I hV hA hB
  exact v_relation_mem_l I hV hδ hY fun p hp =>
    (hP p).mp hp |>.elim fun a ha => ha.2.elim fun b hb => ⟨a, hAY a ha.1, b, hBY b hb.1, hb.2⟩

/-- Kuratowski 图的定义域不增加秩；无需极限层假设。 -/
theorem ZF.v_domain_mem_l (hZF : M.Models ZF) {δ V D F} (hV : V_d I δ V)
    (hF : M.mem F V)
    (hD : M.IsDomainOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) D F) :
    M.mem D V := by
  obtain ⟨β, W, hβ, hW, sub⟩ := (v_unfold_l I hZF hV F).mp hF
  refine (v_unfold_l I hZF hV D).mpr ⟨β, W, hβ, hW, fun x hx => ?_⟩
  obtain ⟨y, p, code, hp⟩ := (hD x).mp hx
  exact (code.mem_l M (v_transitive_l I hW) (sub p hp)).1

theorem ZF.v_restriction_mem_l (hZF : M.Models ZF) {δ V D F H} (hV : V_d I δ V)
    (hF : M.mem F V)
    (hH : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) H F D) :
    M.mem H V := by
  apply v_subset_mem_l I hV hF
  intro p hp
  obtain ⟨x, y, code⟩ := hH.1 p hp
  obtain ⟨q, hq, hqF⟩ := ((hH.2 x y).mp ⟨p, code, hp⟩).2
  exact kpair_unique_l M hZF.1 hq code ▸ hqF

theorem ZF.v_fseq_mem_l (hZF : M.Models ZF) {δ V ω A J} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hω : M.IsOmega ω) (hωV : M.mem ω V) (hA : M.mem A V)
    (hJ : Fseq_space_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω A J) : M.mem J V := by
  obtain ⟨Y, hY, hωY, hAY⟩ := v_joint_bound_l I hV hωV hA
  apply v_relations_mem_l I hV hδ hY
  intro f hf p hp
  obtain ⟨n, hn, fn⟩ := (hJ f).mp hf
  obtain ⟨a, b, code⟩ := fn.1.1 p hp
  exact ⟨a, hωY a (hω.transitive (ZF.modelsKP hZF) n hn a (fn.input_mem_of_pairMember ⟨p, code, hp⟩)),
    b, hAY b (fn.output_mem_of_pairMember ⟨p, code, hp⟩), code⟩

theorem ZF.v_fibers_mem_l (hZF : M.Models ZF) {δ V R B T} (hV : V_d I δ V)
    (hδ : M.IsLimitOrdinal δ) (hR : M.mem R V) (hT : InnerModel.Rd_fun_d .fibers R B R T) : M.mem T V := by
  obtain ⟨β, Y, hβ, hy, hRY⟩ := (v_unfold_l I hZF hV R).mp hR
  have ht := v_transitive_l I hy
  obtain ⟨P, hp⟩ := exists_powerSet hZF Y
  apply v_subset_mem_l I hV (v_power_mem_l I hV hδ (v_mem_l I hZF hy hV hβ) hp)
  intro t h
  obtain ⟨b, _, fiber⟩ := (hT t).mp h
  apply (hp t).mpr
  intro x hx
  obtain ⟨p, code, hpr⟩ := (fiber x).mp hx
  obtain ⟨s, hs, hxs⟩ := (kpair_union_l M code x).mpr (Or.inl rfl)
  exact ht s (ht p (hRY p hpr) s hs) x hxs

end YesMetaZFC.SetTheory
