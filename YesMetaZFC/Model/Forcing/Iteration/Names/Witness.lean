import YesMetaZFC.Model.Forcing.Iteration.Stage.Basic
import YesMetaZFC.Model.Forcing.TwoStep.Witness

/-! # 固定前缀的后继见证装配

直接消费递归系统实际使用的 Row_next_d。名称库、二步条件与坐标编码均从
该证书中提取；输出的前缀等于输入对象本身，并保留所需的第二坐标力迫。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {α B R e A T t D V : M.Domain}

/-- 给定第二坐标名称，原 ZF 即可装配解释相同且前缀精确不变的实际后继条件。 -/
theorem row_next_represent_l (hZF : M.Models ZF) (h : Row_stage_d M α B R e)
    (hNext : Row_next_d M α B R e A T t D V) {p v} (hp : M.mem p B)
    (hv : Name_d M B v) (hm : Mem_force_d M B R B p v A) :
    ∃ s q, Name_d M B s ∧ Row_append_d M α t p s q ∧ M.mem q D ∧
      M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α ∧
      Eq_force_d M B R B p s v := by
  obtain ⟨W, C, S, hW, hStep, hRepr⟩ := hNext
  have hz : p ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp)
  obtain ⟨s, c, hs, hc, hcC, he⟩ := two_step_represent_l h.order hZF hStep hW hv ⟨hp, hz, h.top p hp⟩ hm
  obtain ⟨q, hq⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t p s
  exact ⟨s, q, ⟨W, hs, hStep.closed⟩, hq, (hRepr.conditions q).mpr ⟨c, hcC, p, s, hc, hq⟩,
    ⟨(h.rows p hp).graph, row_append_prefix_l (KP.mem_irrefl_d (ZF.modelsKP hZF) α) (h.rows p hp) hq⟩, he⟩

/-- 从原有界存在公式一次取得后继条件、精确前缀以及满足正文的坐标名称。 -/
theorem row_next_witness_l (hZFC : M.Models ZFC) (h : Row_stage_d M α B R e) {n}
    (φ : UnarySchema n) (ρ : Env M n) (i : Fin n) (hρ : ∀ j, Name_d M B (ρ.bound j))
    (hNext : Row_next_d M α B R e (ρ.bound i) T t D V) {p} (hp : M.mem p B)
    (hex : Forces_d M B R B (.existsE (.conj (.mem .newest (Term.bound i).weaken) φ.body)) ρ p) :
    ∃ s q, Name_d M B s ∧ Row_append_d M α t p s q ∧ M.mem q D ∧
      M.IsRestrictionOf (kpair_interpretation_l M hZFC.1
        (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) p q α ∧
      Forces_d M B R B φ.body (ρ.push s) p := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨W, C, S, hW, hStep, hRepr⟩ := hNext
  have hz : p ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp)
  obtain ⟨s, c, hs, hc, hcC, hφ⟩ := two_step_witness_l h.order hZFC φ ρ i hρ hStep hW ⟨hp, hz, h.top p hp⟩ hex
  obtain ⟨q, hq⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t p s
  exact ⟨s, q, ⟨W, hs, hStep.closed⟩, hq, (hRepr.conditions q).mpr ⟨c, hcC, p, s, hc, hq⟩,
    ⟨(h.rows p hp).graph, row_append_prefix_l (KP.mem_irrefl_d (ZF.modelsKP hZF) α) (h.rows p hp) hq⟩, hφ⟩

/-- 第二坐标的已给加强名称提升为实际后继加强，指定的新前缀 p 原样保留。 -/
theorem row_next_lower_name_l (hZF : M.Models ZF) (h : Row_stage_d M α B R e)
    (hNext : Row_next_d M α B R e A T t D V) (hT : Name_d M B T) {r a s p v}
    (hr : M.mem r D) (ha : M.mem a B) (har : Row_append_d M α t a s r)
    (hp : M.mem p B) (hpa : Entry_d M p a R) (hv : Name_d M B v)
    (hm : Mem_force_d M B R B p v A) (hle : Rel_force_d M B R B T p v s) :
    ∃ w q, Name_d M B w ∧ Row_append_d M α t p w q ∧ M.mem q D ∧ Entry_d M q r V ∧
      M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α ∧
      Eq_force_d M B R B p w v := by
  obtain ⟨W, C, S, hW, hStep, hRepr⟩ := hNext
  obtain ⟨c, hc, a', s', hca, har'⟩ := (hRepr.conditions r).mp hr
  have ha' := ((two_step_mem_l hStep hca).mp hc).2.1.1
  have hα := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  obtain ⟨he, hs⟩ := row_append_injective_l hZF.1 hα (h.rows a ha) (h.rows a' ha') har har'
  subst a'
  subst s'
  have hz : p ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp)
  obtain ⟨w, d, hw, hdp, hd, hdc, he⟩ := two_step_lower_name_l h.order hZF hStep hW hT hc hca
    ⟨hp, hz, hpa⟩ hv hm hle
  obtain ⟨q, hq⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t p w
  have hdq : Row_code_d M α t d q := ⟨p, w, hdp, hq⟩
  exact ⟨w, q, ⟨W, hw, hStep.closed⟩, hq, (hRepr.conditions q).mpr ⟨d, hd, hdq⟩,
    (hRepr.relation q r).mpr ⟨d, c, hd, hc, hdq, ⟨a, s, hca, har⟩, hdc⟩,
    ⟨(h.rows p hp).graph, row_append_prefix_l hα (h.rows p hp) hq⟩, he⟩

end YesMetaZFC.Model.Forcing.Internal
