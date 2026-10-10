import YesMetaZFC.Model.Forcing.Proper.Elementary.RowMap
import YesMetaZFC.Model.Forcing.TwoStep.Proper.Composition
import YesMetaZFC.Model.Forcing.Iteration.Names.Witness

/-! # 坐标后继的固定前缀主条件

主条件先在真实二步偏序中合成，再沿 N 内的实际重编码图搬到坐标阶段。
名称库代表只改变第二坐标的名称，首坐标及其作为限制图的对象精确保留。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω χ H c J d N K α t C S D V : M.Domain}
variable (hω : M.IsOmega ω)
  (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ)
  (hωχ : M.mem ω χ)
  (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
  (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y J ↔
    M.mem x H ∧ M.mem y H ∧ M.mem x y)
  (hSub : Ssub_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) c d H J N K)
  (hElem : Selem_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω c d)
  (hαN : M.mem α N) (htN : M.mem t N) (hCN : M.mem C N) (hDN : M.mem D N)
include hω hχ hωχ hH hJ hSub hElem hαN htN hCN hDN

theorem selem_row_repr_l {B R z b A T} (h : Two_step_d M B R z b A T W C S)
    (hrow : ∀ p, M.mem p B → Row_d M α p) (k : Row_repr_d M α t C S D V) : ∃ F,
    M.mem F N ∧ M.IsSetBijectionFromTo I F C D ∧
    (∀ x q, Entry_d M x q F ↔ M.mem x C ∧ Row_code_d M α t x q) ∧
    ∀ x y p q, Entry_d M x p F → Entry_d M y q F → (Entry_d M p q V ↔ Entry_d M x y S) := by
  obtain ⟨F, hF, hf, he⟩ := row_repr_map_l hZF h hrow k
  have hMap : Row_map_d M α t C D F := by
    refine ⟨fun v hv => ?_, fun x q hx _ => (hf x q).trans (and_iff_right hx)⟩
    obtain ⟨x, q, hvp⟩ := hF.1.1.1.1 v hv
    have hxq : Entry_d M x q F := ⟨v, hvp, hv⟩
    exact ⟨x, q, hF.1.1.input_mem_of_pairMember hxq, hF.1.1.output_mem_of_pairMember hxq, hvp⟩
  have hFN := selem_row_map_l hZFC hω hχ hωχ hH hJ hSub hElem hαN htN hCN hDN hMap
  exact ⟨F, hFN, hF, hf, he⟩

theorem row_repr_master_l {B R z b A T x q} (h : Two_step_d M B R z b A T W C S)
    (hrow : ∀ p, M.mem p B → Row_d M α p) (k : Row_repr_d M α t C S D V)
    (hm : Mstr_d M C S C N x) (hxq : Row_code_d M α t x q) : Mstr_d M D V D N q := by
  obtain ⟨F, hFN, hF, hf, he⟩ := selem_row_repr_l hZFC hω hχ hωχ hH hJ hSub hElem hαN htN hCN hDN h hrow k
  exact mstr_map_l hZF hω hχ.isLimitOrdinal hH hJ hSub hElem hCN hFN hF he hm ((hf x q).mpr ⟨hm.1, hxq⟩)

/-- N 中的坐标条件经实际逆图解码，其原前缀和第二坐标名称仍属于 N。 -/
theorem row_repr_coords_mem_l {B R z b A T x q p s} (h : Two_step_d M B R z b A T W C S)
    (hrow : ∀ p, M.mem p B → Row_d M α p) (k : Row_repr_d M α t C S D V)
    (hx : M.mem x C) (hxq : Row_code_d M α t x q) (hxp : KPair_d M x p s) (hqN : M.mem q N) :
    M.mem p N ∧ M.mem s N := by
  obtain ⟨F, hFN, hF, hf, _⟩ := selem_row_repr_l hZFC hω hχ hωχ hH hJ hSub hElem hαN htN hCN hDN h hrow k
  have htr := ZF.h_transitive_l I hZF hH
  have hxF := (hf x q).mpr ⟨hx, hxq⟩
  obtain ⟨y, hyN, hyF⟩ := selem_entry_witness_l I hJ htr hZF hω hSub hElem hFN hqN ⟨x, hxF⟩
  have hyx := hF.1.2 y x q hyF hxF
  exact selem_kpair_coords_l I hZF hω htr hJ hSub hElem (hyx ▸ hyN) hxp

/-- 保留给定主前缀 p，把任意被迫的 N[G] 主条件名称装入实际坐标后继。 -/
theorem row_step_master_l {B R e A T W p μ v}
    (hB : M.mem B N) (hR : M.mem R N) (h : Row_stage_d M α B R e)
    (hStep : Two_step_d M B R B e A T W C S) (hPool : Name_pool_d M B A t W)
    (k : Row_repr_d M α t C S D V) (L : Cond_order_d M D V D) (hT : Name_d M B T)
    (hm : Mstr_d M B R B N p) (hμ : Ng_name_d M B N μ) (hv : Name_d M B v)
    (hvA : Mem_force_d M B R B p v A)
    (hvM : Forces_d M B R B mstr_body_m (mstr_env_l A T μ v) p) :
    ∃ s q, Name_d M B s ∧ Row_append_d M α t p s q ∧ M.mem q D ∧
      M.IsRestrictionOf I p q α ∧ Mstr_d M D V D N q ∧ Eq_force_d M B R B p s v := by
  obtain ⟨s, x, hs, hxp, hx, hsv⟩ := two_step_represent_l h.order hZF hStep hPool hv
    ⟨hm.1, hm.2.1, h.top p hm.1⟩ hvA
  have hsN : Name_d M B s := ⟨W, hs, hStep.closed⟩
  let ρ : Env M 3 := ((⟨fun _ => A, fun _ => A⟩ : Env M 1).push T).push μ
  let φ : UnarySchema 3 := { body := mstr_body_m, freeClosed := mstr_body_closed_l }
  have hA : Name_d M B A := ⟨W, hStep.root, hStep.closed⟩
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases hμ.1 (Fin.cases hT (fun _ => hA))
  have hsM := (forces_name_congr_l h.order hZF φ ρ hρ hv hsN hm.1 hm.2.1
    (eq_force_symm_l hZF hsN hv hsv)).mp hvM
  have hxM := two_step_master_l h.order hZFC hω hχ hωχ hH hJ hSub hElem hB hR hB hStep
    (row_repr_order_l hZF hStep h.rows k L) hT hx hxp hm hμ hsM
  obtain ⟨q, hq⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t p s
  have hxq : Row_code_d M α t x q := ⟨p, s, hxp, hq⟩
  exact ⟨s, q, hsN, hq, (k.conditions q).mpr ⟨x, hx, hxq⟩,
    ⟨(h.rows p hm.1).graph, row_append_prefix_l (KP.mem_irrefl_d (ZF.modelsKP hZF) α) (h.rows p hm.1) hq⟩,
    row_repr_master_l hZFC hω hχ hωχ hH hJ hSub hElem hαN htN hCN hDN hStep h.rows k hxM hxq, hsv⟩

/-- 在指定的主前缀 p 上选择后继主加强，同时低于原坐标条件；无需再次加强 p。 -/
theorem row_step_lower_master_l {B R e A T W r a u p μ}
    (hB : M.mem B N) (hR : M.mem R N) (h : Row_stage_d M α B R e)
    (hStep : Two_step_d M B R B e A T W C S) (hPool : Name_pool_d M B A t W)
    (k : Row_repr_d M α t C S D V) (L : Cond_order_d M D V D) (hT : Name_d M B T)
    (hr : M.mem r D) (ha : M.mem a B) (har : Row_append_d M α t a u r) (hpa : Entry_d M p a R)
    (hm : Mstr_d M B R B N p) (hμ : Ng_name_d M B N μ)
    (hex : Forces_d M B R B (.existsE (.conj (.mem .newest (.bound 4)) mstr_lower_s.body))
      (mstr_env_l A T μ u) p) :
    ∃ s q, Name_d M B s ∧ Row_append_d M α t p s q ∧ M.mem q D ∧ Entry_d M q r V ∧
      M.IsRestrictionOf I p q α ∧ Mstr_d M D V D N q ∧
      Forces_d M B R B mstr_lower_s.body ((mstr_env_l A T μ u).push s) p := by
  obtain ⟨x, hx, a', u', hxa, har'⟩ := (k.conditions r).mp hr
  have ha' := ((two_step_mem_l hStep hxa).mp hx).2.1.1
  have hα := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  obtain ⟨he, hu⟩ := row_append_injective_l hZF.1 hα (h.rows a ha) (h.rows a' ha') har har'
  subst a' u'
  have huN : Name_d M B u := ⟨W, ((two_step_mem_l hStep hxa).mp hx).1, hStep.closed⟩
  have hA : Name_d M B A := ⟨W, hStep.root, hStep.closed⟩
  let ρ := mstr_env_l A T μ u
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases huN (Fin.cases hμ.1 (Fin.cases hT (fun _ => hA)))
  obtain ⟨s, y, hs, hyp, hy, hsF⟩ := two_step_witness_l h.order hZFC mstr_lower_s ρ 3 hρ hStep hPool
    ⟨hm.1, hm.2.1, h.top p hm.1⟩ hex
  obtain ⟨hsu, hsM⟩ := force_mstr_lower_l hZF.1 hsF
  have hyM := two_step_master_l h.order hZFC hω hχ hωχ hH hJ hSub hElem hB hR hB hStep
    (row_repr_order_l hZF hStep h.rows k L) hT hy hyp hm hμ hsM
  obtain ⟨q, hq⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t p s
  have hyq : Row_code_d M α t y q := ⟨p, s, hyp, hq⟩
  have hyx := (two_step_le_l hStep hy hx hyp hxa).mpr ⟨⟨hm.1, hm.2.1, hpa⟩, hsu⟩
  exact ⟨s, q, ⟨W, hs, hStep.closed⟩, hq, (k.conditions q).mpr ⟨y, hy, hyq⟩,
    (k.relation q r).mpr ⟨y, x, hy, hx, hyq, ⟨a, u, hxa, har⟩, hyx⟩,
    ⟨(h.rows p hm.1).graph, row_append_prefix_l hα (h.rows p hm.1) hq⟩,
    row_repr_master_l hZFC hω hχ hωχ hH hJ hSub hElem hαN htN hCN hDN hStep h.rows k hyM hyq, hsF⟩

end YesMetaZFC.Model.Forcing.Internal
