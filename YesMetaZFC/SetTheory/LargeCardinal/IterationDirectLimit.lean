import YesMetaZFC.SetTheory.LargeCardinal.IterationSystem
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Elementary

/-! # 树枝的实际直接极限及全部规范初等嵌入

先把旧嵌入经标签同构搬到各分量，再取实际集合商。规范嵌入保留精确
代表方程，因此极限覆盖与交换律可从同一批商类直接读出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_system_d.elementary_l {ω α T Q G B L A p H R : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (s : It_system_d B L Q G A p H R)
    (inside : M.MemberSubset B α)
    (ls : ∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) :
    Di_elementary_d I ω L A p H R := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  intro i j c X S d Y V si sj hij
  obtain ⟨hi, hj, hij⟩ := (ls i j).mp hij
  obtain ⟨c₀, X₀, S₀, hc, mx⟩ := h.model_l hZF (inside i hi)
  obtain ⟨d₀, Y₀, V₀, hd, my⟩ := h.model_l hZF (inside j hj)
  obtain ⟨f, hf⟩ := h.map_l hZF hij
  have elem := h.elementary i j f c₀ X₀ S₀ d₀ Y₀ V₀ hf hc hd mx my
  obtain ⟨e, _, he, _, es, _⟩ := it_tag_iso_l hZF hω s.tags hq si hc mx
  obtain ⟨_, u, _, hu, _, us⟩ := it_tag_iso_l hZF hω s.tags hq sj hd my
  obtain ⟨v, hv, vs⟩ := smap_comp_l I hZF he elem
  obtain ⟨w, hw, ws⟩ := smap_comp_l I hZF hv hu
  refine ⟨w, hw, fun a b => ⟨?_, ?_⟩⟩
  · intro hab
    obtain ⟨ha, y, hay, hyb⟩ := (ws a b).mp hab
    obtain ⟨_, x, hax, hxy⟩ := (vs a y).mp hay
    obtain ⟨_, hp⟩ := (es a x).mp hax
    obtain ⟨hb, hq'⟩ := (us y b).mp hyb
    exact ⟨ha, hb, (s.arrows a b i j x y hp hq').mpr
      ⟨((si.2.1 a).mp ha).1, ((sj.2.1 b).mp hb).1, f, hf, hxy⟩⟩
  · rintro ⟨ha, hb, hab⟩
    obtain ⟨x, hp, _⟩ := s.tags.label_l (((si.2.1 a).mp ha).2)
    obtain ⟨y, hq', _⟩ := s.tags.label_l (((sj.2.1 b).mp hb).2)
    obtain ⟨g, hg, hxy⟩ := ((s.arrows a b i j x y hp hq').mp hab).2.2
    have hxy := h.map_unique_l hZF hg hf ▸ hxy
    exact (ws a b).mpr ⟨ha, y, (vs a y).mpr ⟨ha, x, (es a x).mpr ⟨ha, hp⟩, hxy⟩,
      (us y b).mpr ⟨hb, hq'⟩⟩

theorem it_stage_limit_l {ω α T Q G B L A p H R q c C V i d X S : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (s : It_system_d B L Q G A p H R)
    (elementary : Di_elementary_d I ω L A p H R)
    (limit : Di_limit_d A p H R q C V) (model : Smdl_d I c C V)
    (hi : M.mem i B) (hd : Rd_entry_d i d Q) (mx : Smdl_d I d X S) :
    ∃ j, Smap_d I ω d c X C j ∧
      ∀ x y, Rd_entry_d x y j ↔ M.mem x X ∧ ∃ a, KPair_d M a i x ∧ Rd_entry_d a y q := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  obtain ⟨x, hx⟩ := mx.2.1
  obtain ⟨a, hp⟩ := (I).total i x
  have ha := (s.tags.nodes a).mpr ⟨i, x, hi, hp, d, X, S, hd, mx.1, hx⟩
  obtain ⟨d', Y, W, stage⟩ := di_stage_exists_l hZF s.system ((s.tags.index a i x hp).mpr ha)
  obtain ⟨_, u, _, hu, _, us⟩ := it_tag_iso_l hZF hω s.tags hq stage hd mx
  obtain ⟨e, he, es⟩ := di_elementary_limit_l hZF hω s.system limit elementary stage model
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF hu he
  refine ⟨j, hj, fun x y => (js x y).trans (and_congr_right fun hx => ?_)⟩
  apply exists_congr
  intro a
  refine ⟨fun ⟨hxa, hay⟩ => ⟨((us x a).mp hxa).2, ((es a y).mp hay).2⟩, fun ⟨hp, hay⟩ => ?_⟩
  have ha := (s.tags.nodes a).mpr ⟨i, x, hi, hp, d, X, S, hd, mx.1, hx⟩
  have haY := (stage.2.1 a).mpr ⟨ha, (s.tags.index a i x hp).mpr ha⟩
  exact ⟨(us x a).mpr ⟨haY, hp⟩, (es a y).mpr ⟨haY, hay⟩⟩

/-- 非空树枝的原始极限总能实际构造；其良基性留给独立的数学判据证明。 -/
theorem it_branch_data_l {ω α T Q G B : M.Domain} (hω : M.IsOmega ω)
    (h : It_diagram_d hZF ω α T Q G) (b : It_branch_d α T B) (ne : ∃ i, M.mem i B) :
    ∃ L A p H R q c C V,
      (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
      It_system_d B L Q G A p H R ∧ Di_elementary_d I ω L A p H R ∧
      Di_limit_d A p H R q C V ∧ Smdl_d I c C V := by
  obtain ⟨L, order, ls⟩ := b.order_l (ZF.modelsKP hZF) h.order
  obtain ⟨A, p, H, R, s⟩ := it_system_l hZF hω h order b.subset ls
  obtain ⟨i, hi⟩ := ne
  obtain ⟨d, X, S, hd, mx⟩ := h.model_l hZF (b.subset i hi)
  obtain ⟨x, hx⟩ := mx.2.1
  obtain ⟨a, hp⟩ := (I).total i x
  have ha := (s.tags.nodes a).mpr ⟨i, x, hi, hp, d, X, S, hd, mx.1, hx⟩
  obtain ⟨c, q, C, V, limit, model⟩ := di_model_exists_l hZF s.system ⟨a, ha⟩
  exact ⟨L, A, p, H, R, q, c, C, V, ls, s, s.elementary_l hZF hω h b.subset ls, limit, model⟩

end YesMetaZFC.SetTheory.LargeCardinal
