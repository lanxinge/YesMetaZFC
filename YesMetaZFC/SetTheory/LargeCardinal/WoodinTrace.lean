import YesMetaZFC.SetTheory.LargeCardinal.WoodinStrength
import YesMetaZFC.Model.SetTheory.Internal.PredicateTrace

/-! # 武丁强扩展器对谓词截面的作用

给真值码谓词加入一个序数标记 α。低秩一致性和截面初等性迫使 α 固定，
而强度超过 α，故临界点严格大于 α。标记不进入由有序对组成的类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 在强度以下只有一个序数标记时，该标记严格低于临界点。 -/
theorem Ep_strength_d.above_l (hZF : M.Models ZF)
    {ω δ κ L X R A V j Y q c C W α : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X)
    (hL : M.IsOrdinal L) (hLX : M.mem L X) (hα : M.mem α L) (hαV : M.mem α V)
    (marker : ∀ x, M.mem x L → (M.mem x A ↔ x = α))
    (h : Ep_strength_d hZF ω κ L X R A V j Y q c C W) : M.mem α κ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨b, d, N, S, B, i, k, κ', hm, hn, hN, hi, embed, crit, bound, _, _, _, _, _, _, _, _, agree, _⟩ := h
  have ht := ZF.v_transitive_l I hZF hX
  have hαX := ht L hLX α hα
  obtain ⟨a, _, ha⟩ := hi.1.1.2.2 α hαX
  obtain ⟨D, _, hD⟩ := hi.1.1.2.2 L hLX
  obtain ⟨t, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) α α
  have singleton x : M.mem x t ↔ x = α := (pair x).trans ⟨fun hh => hh.elim id id, Or.inl⟩
  have htX := ZF.v_subset_mem_l I hZF hX hLX (fun x hx => (singleton x).mp hx ▸ hα)
  obtain ⟨t', _, htt⟩ := hi.1.1.2.2 t htX
  have trace x : M.mem x t ↔ M.mem x L ∧ M.mem x A := (singleton x).trans
    ⟨fun eq => ⟨eq ▸ hα, (marker x (eq ▸ hα)).mpr eq⟩, fun hh => (marker x hh.1).mp hh.2⟩
  have image := spred_trace_l I hZF hω embed hN hD htt trace
  have αD := hi.ordinal_le_l hZF hω ht hN hm hn hD hL α hα
  have αB := (agree α hαV).mp ((marker α hα).mpr rfl)
  have tr := spred_delta_l I hZF hω embed ht hN (n := 2)
    (Formula.forallMem (.bound 1) (Formula.extensionalEq .newest (.bound 1)))
    (by simp) (.forallMem _ (.atom _ _ _))
    ⟨Fin.cases α (fun _ => t), fun _ => α⟩ ⟨Fin.cases a (fun _ => t'), fun _ => a⟩
    (Fin.cases ha (fun _ => htt))
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1] at tr
  have eq : α = a := tr.mp (fun x hx => (singleton x).mp hx) α ((image α).mpr ⟨αD, αB⟩)
  subst a
  rcases Structure.IsOrdinal.trichotomy hZF.1 (hL.mem hα) crit.ordinal
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) α κ) with he | he | he
  · have e := hZF.1.eq_of_same_members α κ he
    exact (crit.moved (hi.1.1.1.2 κ κ κ' (e ▸ ha) crit.image)).elim
  · exact he
  · have hkα := (ed_member_l I hZF hω embed ht hN crit.image ha).mp he
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) κ'
      (crit.ordinal_image.transitive α (bound α hα) κ' hkα)).elim

/-- 任意关系码谓词都可加标记；所得强扩展器的临界点超过给定 α。
    C 的完整定义及原强度证书一同返回，类型截面随后可直接消费它们。 -/
theorem woodin_marked_strength_l (hZFC : M.Models ZFC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → M.IsSetRelation I A →
      ∀ α, M.mem α δ → ∃ C κ, (∀ p, M.mem p C ↔ M.mem p A ∨ p = α) ∧ M.mem α κ ∧ M.mem κ δ ∧
        ∀ ν, M.mem ν δ → ∃ L K F R V Y j, M.mem L δ ∧ M.mem κ L ∧ M.mem ν L ∧ M.mem ω L ∧
          M.IsRegularCardinal I L ∧ M.IsStrongLimitCardinal I L ∧ V_d I L V ∧
          Ex_short_d hZF ω κ L F ∧ Ep_source_d hZF ω κ K X R ∧ Ep_strong_limit_d hZF ω κ L X R C V F j Y := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, hω, hX, all⟩ := woodin_rank_strength_l hZFC hd
  refine ⟨ω, X, hω, hX, fun A hA rel α hα => ?_⟩
  let φ : UnarySchema 2 := { body := .disj (.mem .newest (.bound 2)) (Formula.extensionalEq .newest (.bound 1)) }
  let ρ : Env M 2 := ⟨Fin.cases α (fun _ => A), fun _ => A⟩
  obtain ⟨C, sep⟩ := ZF.separation_exists_d hZF φ ρ X
  have spec p : M.mem p C ↔ M.mem p A ∨ p = α := by
    have eq : φ.denote ρ p ↔ M.mem p A ∨ p = α := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
        Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
    exact (sep p).trans ((and_congr_right fun _ => eq).trans
      ⟨And.right, fun hp => ⟨hp.elim (hA p) (fun he => he ▸ ZF.v_ordinal_mem_l I hZF hX hα), hp⟩⟩)
  obtain ⟨κ, hκ, family⟩ := all C (fun p hp => ((sep p).mp hp).1)
  obtain ⟨L, K, F, R, V, Y, j, hL, _, hαL, _, rL, _, hV, _, _, strong⟩ := family α hα
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, strength, _⟩ := strong
  have above := strength.above_l hZF hω hX rL.isCardinal.1 (ZF.v_ordinal_mem_l I hZF hX hL)
    hαL (ZF.v_ordinal_mem_l I hZF hV hαL) (fun x hx => (spec x).trans
      ⟨fun hh => hh.elim (fun ha => by
        obtain ⟨a, b, pair⟩ := rel x ha
        exact (pair.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF)) (rL.isCardinal.1.mem hx).transitive).elim) id,
        Or.inr⟩)
  exact ⟨C, κ, spec, above, hκ, family⟩

end YesMetaZFC.SetTheory.LargeCardinal
