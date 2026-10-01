import YesMetaZFC.Model.Forcing.Iteration.Stage.Next
import YesMetaZFC.Model.Forcing.Iteration.Condition.Projection
import YesMetaZFC.Model.Forcing.TwoStep.Embedding
import YesMetaZFC.Model.Forcing.Stage.Composition

/-! # 具有共同顶条件的内部坐标阶段

零阶段和任意名称后继阶段均实际构造。省略顶坐标使旧条件按原对象嵌入新阶段，
并保持同一个顶条件；每个新条件限制到旧索引集时仍是旧阶段条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

structure Row_stage_d (M : SetTheory.Structure.{u}) (α B R e : M.Domain) : Prop where
  order : Cond_order_d M B R B
  base : M.mem e B
  top : ∀ p, M.mem p B → Entry_d M p e R
  rows : ∀ p, M.mem p B → Row_d M α p

def row_stage_m {n} (α B R e : Term n) : Formula 1 n :=
  .conj (cond_order_m B R B) (.conj (.mem e B)
    (.conj (.forallE (.imp (.mem .newest B.weaken) (entry_m .newest e.weaken R.weaken)))
      (.forallE (.imp (.mem .newest B.weaken) (row_m α.weaken .newest)))))
derive_free_closed row_stage_m

theorem row_stage_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (α B R e : Term n) : Formula.satisfies ρ (row_stage_m α B R e) ↔
      Row_stage_d M (α.eval ρ) (B.eval ρ) (R.eval ρ) (e.eval ρ) := by
  simp only [row_stage_m, Formula.satisfies_conj_iff, cond_order_sat_l hE, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, entry_sat_l M hE, row_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun hh => ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2⟩, fun hh => ⟨hh.order, hh.base, hh.top, hh.rows⟩⟩

/-- 实际零阶段只有空函数；两种支撑大小都由原模型中的空定义域验证。 -/
theorem row_zero_l (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) : ∃ e B R,
    (∀ x, ¬ M.mem x e) ∧ Row_stage_d M e B R e ∧
      ∀ {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) k ω, M.IsOmega ω →
        ∀ p, M.mem p B → Row_supp_d I k ω p := by
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨B, hB⟩ := KP.exists_pair (ZF.modelsKP hZF) e e
  have eq {p} (hp : M.mem p B) : p = e := ((hB p).mp hp).elim id id
  have hb := (hB e).mpr (Or.inl rfl)
  obtain ⟨R, hR, O, _⟩ := subset_order_l M hZF B
  refine ⟨e, B, R, he, ⟨O, hb, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact (hR p e).mpr ⟨hp, hb, fun x hx => False.elim (he x hx)⟩
  · intro p hp
    have hp' := eq hp
    subst p
    exact row_empty_l M he
  · intro 𝒞 I k ω hω p hp
    have hp' := eq hp
    subst p
    exact row_supp_empty_l I hZF hω he k

/-- 任意名称预序的真实后继，返回限制投影、保留尾部的加强和两类支撑保持。 -/
theorem row_successor_l {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
    {α β B R e A T t : M.Domain} (h : Row_stage_d M α B R e) (hβ : M.SuccessorOf β α)
    (hA : Name_d M B A) (hT : Name_d M B T) (ht : Name_d M B t)
    (hP : Forces_d M B R B (preord_m .newest (.bound 1)) (ord_env_l M A T) e)
    (hTop : Forces_d M B R B (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) e) :
    ∃ D V G, Row_stage_d M β D V e ∧ Row_next_d M α B R e A T t D V ∧ Reg_embed_d M B R B D V D G ∧
      (∀ p q, Entry_d M p q G ↔ M.mem p B ∧ q = p) ∧
      Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V ∧
      ∀ {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) k ω, M.IsOmega ω →
        (∀ p, M.mem p B → Row_supp_d I k ω p) → ∀ q, M.mem q D → Row_supp_d I k ω q := by
  have nz {p} (hp : M.mem p B) : p ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp)
  have below {p} (hp : M.mem p B) : Below_d M B R B p e := ⟨hp, nz hp, h.top p hp⟩
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hα := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  obtain ⟨W, C, S, hStep, L, hHull, c₀, hc₀e, hc₀, hc₀top⟩ :=
    two_step_pointed_l h.order hZF hA hT ht h.base (nz h.base) hP hTop
  obtain ⟨D, V, F, hD, hF, _, hGraph, hV, K, hReg, hRow, hPre, hSupp⟩ :=
    two_step_rows_l (t := t) hZF hStep L hβ h.rows
  have repr : Row_repr_d M α t C S D V := ⟨hD, hGraph, fun p q => (hV p q).trans (by
    constructor
    · rintro ⟨c, d, hcp, hdq, hcd⟩
      obtain ⟨hc, hcp⟩ := (hF c p).mp hcp
      obtain ⟨hd, hdq⟩ := (hF d q).mp hdq
      exact ⟨c, d, hc, hd, hcp, hdq, hcd⟩
    · rintro ⟨c, d, hc, hd, hcp, hdq, hcd⟩
      exact ⟨c, d, (hF c p).mpr ⟨hc, hcp⟩, (hF d q).mpr ⟨hd, hdq⟩, hcd⟩)⟩
  have hc₀F : Entry_d M c₀ e F := (hF c₀ e).mpr ⟨hc₀, e, t, hc₀e, Or.inl ⟨rfl, rfl⟩⟩
  have heD := (hReg.domain c₀ e hc₀F).2.2.1
  have top q (hq : M.mem q D) : Entry_d M q e V := by
    obtain ⟨c, hc, hcode⟩ := (hD q).mp hq
    exact (hV q e).mpr ⟨c, c₀, (hF c q).mpr ⟨hc, hcode⟩, hc₀F, hc₀top c hc⟩
  obtain ⟨P, H, hP', hH, hEmbed⟩ := two_step_embed_l h.order hZF hStep L hT hHull.right hTop
  have hPB : P = B := hZF.1.eq_of_same_members P B (fun p => (hP' p).trans ⟨And.left, below⟩)
  subst P
  obtain ⟨G, hG, hGReg⟩ := reg_embed_comp_l hZF K hEmbed hReg
  have id p q : Entry_d M p q G ↔ M.mem p B ∧ q = p := by
    constructor
    · intro hpq
      obtain ⟨c, hpc, hcq⟩ := (hG p q).mp hpq
      obtain ⟨hp, hcp⟩ := (hH p c).mp hpc
      obtain ⟨_, p', s, hcp', happ⟩ := (hF c q).mp hcq
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hcp hcp'
      exact ⟨hp.1, row_append_unique_l M hZF.1 happ (Or.inl ⟨rfl, rfl⟩)⟩
    · rintro ⟨hp, hqp⟩
      subst q
      obtain ⟨c, hcp⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total p t
      have hpc := (hH p c).mpr ⟨below hp, hcp⟩
      exact (hG p p).mpr ⟨c, hpc, (hF c p).mpr
        ⟨(hEmbed.domain p c hpc).2.2.1, p, t, hcp, Or.inl ⟨rfl, rfl⟩⟩⟩
  have decode p a (hp : M.mem p D) (ha : M.IsRestrictionOf I a p α) :
      ∃ c s, M.mem c C ∧ KPair_d M c a s ∧ Row_append_d M α t a s p ∧ Entry_d M c p F := by
    obtain ⟨c, hc, a', s, hca, happ⟩ := (hD p).mp hp
    have haB := ((two_step_mem_l hStep hca).mp hc).2.1.1
    have he := ha.eq hZF.1 ⟨(h.rows a' haB).graph, row_append_prefix_l hα (h.rows a' haB) happ⟩
    subst a'
    exact ⟨c, s, hc, hca, happ, (hF c p).mpr ⟨hc, a, s, hca, happ⟩⟩
  have hn : ∀ v : Term 3, Name_d M B (v.eval (top_env_l A T t)) := by
    intro v
    cases v with
    | free _ => exact hT
    | bound i => exact Fin.cases ht (Fin.cases hA (fun _ => hT)) i
  have under p a (hp : M.mem p D) (ha : M.IsRestrictionOf I a p α) : Entry_d M p a V := by
    obtain ⟨c, s, hc, hca, _, hcp⟩ := decode p a hp ha
    obtain ⟨hs, ha', hsm⟩ := (two_step_mem_l hStep hca).mp hc
    obtain ⟨d, hda⟩ := I.total a t
    have had := (hH a d).mpr ⟨ha', hda⟩
    have hd := (hEmbed.domain a d had).2.2.1
    have hdF := (hF d a).mpr ⟨hd, a, t, hda, Or.inl ⟨rfl, rfl⟩⟩
    have htop := forced_top_l h.order hZF hA hT ht ha'.1 ha'.2.1
      ((forces_regular_l h.order hZF _ _ hn).1 e a h.base ha' hTop)
    exact (hV p a).mpr ⟨c, d, hcp, hdF, (two_step_le_l hStep hc hd hca hda).mpr
      ⟨below_refl_l h.order ha'.1 ha'.2.1, htop.2 s ⟨W, hs, hStep.closed⟩ hsm⟩⟩
  have mono p q a b (hp : M.mem p D) (hq : M.mem q D)
      (ha : M.IsRestrictionOf I a p α) (hb : M.IsRestrictionOf I b q α) (hpq : Entry_d M p q V) :
      Entry_d M a b R := by
    obtain ⟨c, s, hc, hca, _, hcp⟩ := decode p a hp ha
    obtain ⟨d, v, hd, hdb, _, hdq⟩ := decode q b hq hb
    exact ((two_step_le_l hStep hc hd hca hdb).mp ((hReg.order c d p q hcp hdq).mp hpq)).1.2.2
  have link : Row_link_d I α B R D V := {
    rows := h.rows
    mem := fun p hp => (hGReg.domain p p ((id p p).mpr ⟨hp, rfl⟩)).2.2.1
    order := fun p q hp hq => hGReg.order p q p q ((id p p).mpr ⟨hp, rfl⟩) ((id q q).mpr ⟨hq, rfl⟩)
    restrict := hPre
    below := under
    mono := mono
    splice := by
      intro p a q r hp ha hq hqa hr
      obtain ⟨c, s, hc, hca, happ, hcp⟩ := decode p a hp ha
      obtain ⟨d, hdq, hd⟩ := two_step_lift_l h.order hZF hStep L hT hc hca ⟨hq, nz hq, hqa⟩
      obtain ⟨r', hr'⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t q s
      have haB := ((two_step_mem_l hStep hca).mp hc).2.1.1
      have he := row_splice_unique_l M hZF.1 hr (row_append_splice_l hZF.1 hα (h.rows a haB) happ hr')
      subst r'
      have hdr := (hF d r).mpr ⟨hd.1, q, s, hdq, hr'⟩
      have hrD := (hD r).mpr ⟨d, hd.1, q, s, hdq, hr'⟩
      exact ⟨hrD, (hV r p).mpr ⟨d, c, hdr, hcp, hd.2.2⟩,
        under r q hrD ⟨(h.rows q hq).graph, row_append_prefix_l hα (h.rows q hq) hr'⟩⟩
    splice_glb := by
      intro p a q r u hp ha hq hqa hr hu hup huq
      obtain ⟨c, s, hc, hca, happ, hcp⟩ := decode p a hp ha
      obtain ⟨d, hdq, hd⟩ := two_step_lift_l h.order hZF hStep L hT hc hca ⟨hq, nz hq, hqa⟩
      obtain ⟨r', hr'⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t q s
      have haB := ((two_step_mem_l hStep hca).mp hc).2.1.1
      have he := row_splice_unique_l M hZF.1 hr (row_append_splice_l hZF.1 hα (h.rows a haB) happ hr')
      subst r'
      have hdr := (hF d r).mpr ⟨hd.1, q, s, hdq, hr'⟩
      obtain ⟨b, hb, hbu⟩ := hPre u hu
      obtain ⟨v, w, hv, hvb, _, hvu⟩ := decode u b hu hbu
      have hw := ((two_step_le_l hStep hv hc hvb hca).mp ((hReg.order v c u p hvu hcp).mp hup)).2
      have hqD := (hGReg.domain q q ((id q q).mpr ⟨hq, rfl⟩)).2.2.1
      have hqq : M.IsRestrictionOf I q q α := ⟨(h.rows q hq).graph,
        fun i s => ⟨fun hi => ⟨(h.rows q hq).domain i s hi, hi⟩, And.right⟩⟩
      have hbq := mono u q b q hu hqD hbu hqq huq
      exact (hV u r).mpr ⟨v, d, hvu, hdr, (two_step_le_l hStep hv hd.1 hvb hdq).mpr ⟨⟨hb, nz hb, hbq⟩, hw⟩⟩
    tail := by
      intro p q a b hp hq ha hb hab hd
      obtain ⟨c, s, hc, hca, happ, hcp⟩ := decode p a hp ha
      obtain ⟨d, u, hdC, hdb, _, hdq⟩ := decode q b hq hb
      obtain ⟨hsW, ha', _⟩ := (two_step_mem_l hStep hca).mp hc
      have huW := ((two_step_mem_l hStep hdb).mp hdC).1
      refine (hV p q).mpr ⟨c, d, hcp, hdq, (two_step_le_l hStep hc hdC hca hdb).mpr ⟨⟨ha'.1, ha'.2.1, hab⟩, ?_⟩⟩
      apply (rel_force_regular_l h.order hZF hT ⟨W, hsW, hStep.closed⟩ ⟨W, huW, hStep.closed⟩).2 a ha'.1 ha'.2.1
      intro x hx
      obtain ⟨y, hyx, hy⟩ := hd x hx
      have hya := below_trans_l h.order ha'.1 hyx hx
      obtain ⟨v, hvy, hv⟩ := two_step_lift_l h.order hZF hStep L hT hc hca hya
      obtain ⟨r, hr⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t y s
      have hvr := (hF v r).mpr ⟨hv.1, y, s, hvy, hr⟩
      have hrq := hy r (row_append_splice_l hZF.1 hα (h.rows a ha'.1) happ hr)
      exact ⟨y, hyx, ((two_step_le_l hStep hv.1 hdC hvy hdb).mp ((hReg.order v d r q hvr hdq).mp hrq)).2⟩ }
  exact ⟨D, V, G, ⟨K, heD, top, hRow⟩, ⟨W, C, S, hHull, hStep, repr⟩, hGReg, id, link, hSupp⟩

end YesMetaZFC.Model.Forcing.Internal
