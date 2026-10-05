import YesMetaZFC.SetTheory.LargeCardinal.IterationTagIso
import YesMetaZFC.SetTheory.LargeCardinal.IterationBranch

/-! # 树枝上的实际定向系统

带标号的箭头逐值等于旧树嵌入。函数性、单射性、交换律与原子关系的
保持反映均从同一张旧图读出，不在极限处另加这些性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_arrow_d (G i j x y : M.Domain) : Prop := ∃ f, It_map_d G i j f ∧ Rd_entry_d x y f
def it_arrow_m {d} (G i j x y : Term d) : Formula 1 d := .existsE
  (.conj (it_map_m G.weaken i.weaken j.weaken .newest) (rd_entry_m x.weaken y.weaken .newest))
derive_free_closed it_arrow_m

theorem it_arrow_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G i j x y : Term d) :
    Formula.satisfies ρ (it_arrow_m G i j x y) ↔
      It_arrow_d (G.eval ρ) (i.eval ρ) (j.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [it_arrow_m, It_arrow_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    it_map_sat_l hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

structure It_system_d (B L Q G A p H R : M.Domain) : Prop where
  tags : It_tag_d B Q A p R
  system : Di_system_d B L A p H R
  arrows : ∀ u v i j x y, KPair_d M u i x → KPair_d M v j y →
    (Rd_entry_d u v H ↔ M.mem u A ∧ M.mem v A ∧ It_arrow_d G i j x y)

theorem it_system_l (hZF : M.Models ZF) {ω α T Q G B L : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G)
    (order : Di_order_d B L) (inside : M.MemberSubset B α)
    (ls : ∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) :
    ∃ A p H R, It_system_d B L Q G A p H R := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨D, hq⟩ := h.family_l hZF
  obtain ⟨A, p, R, tags⟩ := it_tags_l hZF B Q
  let φ : BinarySchema 1 := { body := .existsE (.existsE (.existsE (.existsE (.conj
    (kpair_m (.bound 5) (.bound 3) (.bound 1)) (.conj (kpair_m (.bound 4) (.bound 2) .newest)
      (it_arrow_m (.bound 6) (.bound 3) (.bound 2) (.bound 1) .newest)))))) }
  obtain ⟨H, _, hs⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ⟨fun _ => G, fun _ => G⟩ A
  have arrows u v : Rd_entry_d u v H ↔ M.mem u A ∧ M.mem v A ∧
      ∃ i j x y, KPair_d M u i x ∧ KPair_d M v j y ∧ It_arrow_d G i j x y := by
    simpa only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, it_arrow_sat_l hZF.1] using! hs u v
  have read u v i j x y (hu : KPair_d M u i x) (hv : KPair_d M v j y) :
      Rd_entry_d u v H ↔ M.mem u A ∧ M.mem v A ∧ It_arrow_d G i j x y := by
    refine (arrows u v).trans ⟨fun ⟨huA, hvA, i', j', x', y', hu', hv', hh⟩ => ?_,
      fun ⟨huA, hvA, hh⟩ => ⟨huA, hvA, i, j, x, y, hu, hv, hh⟩⟩
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu'
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
    exact ⟨huA, hvA, hh⟩
  have bound u v (huv : Rd_entry_d u v H) : M.mem u A ∧ M.mem v A :=
    ⟨((arrows u v).mp huv).1, ((arrows u v).mp huv).2.1⟩
  have node i x (hi : M.mem i B) (hx : Ep_at_d Q i x) : ∃ u, M.mem u A ∧ KPair_d M u i x ∧ Rd_entry_d u i p := by
    obtain ⟨u, hp⟩ := I.total i x
    have hu := (tags.nodes u).mpr ⟨i, x, hi, hp, hx⟩
    exact ⟨u, hu, hp, (tags.index u i x hp).mpr hu⟩
  have get i j f (hf : It_map_d G i j f) : ∃ c X S d Y V,
      Rd_entry_d i c Q ∧ Rd_entry_d j d Q ∧ Smdl_d I c X S ∧ Smdl_d I d Y V ∧ Smap_d I ω c d X Y f := by
    obtain ⟨hi, hj⟩ := h.order.bound i j (h.map_bound_l hZF hf)
    obtain ⟨c, X, S, hc, mx⟩ := h.model_l hZF hi
    obtain ⟨d, Y, V, hd, my⟩ := h.model_l hZF hj
    exact ⟨c, X, S, d, Y, V, hc, hd, mx, my, h.elementary i j f c X S d Y V hf hc hd mx my⟩
  have arrow i j x y f (hf : It_map_d G i j f) : It_arrow_d G i j x y ↔ Rd_entry_d x y f :=
    ⟨fun ⟨g, hg, hxy⟩ => h.map_unique_l hZF hg hf ▸ hxy, fun hxy => ⟨f, hf, hxy⟩⟩
  have forward u v i j (hu : Rd_entry_d u i p) (hv : Rd_entry_d v j p) (huv : Rd_entry_d u v H) : Rd_entry_d i j L := by
    obtain ⟨x, hp, _⟩ := tags.label_l hu
    obtain ⟨y, hq', _⟩ := tags.label_l hv
    obtain ⟨f, hf, _⟩ := ((read u v i j x y hp hq').mp huv).2.2
    exact (ls i j).mpr ⟨(tags.projection.bound_l hu).2, (tags.projection.bound_l hv).2, h.map_bound_l hZF hf⟩
  refine ⟨A, p, H, R, tags, ⟨order, tags.projection, bound, forward, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, read⟩
  · intro u hu
    obtain ⟨i, x, hi, hp, hx⟩ := (tags.nodes u).mp hu
    obtain ⟨f, hf⟩ := h.map_l hZF (h.order.refl i (inside i hi))
    obtain ⟨c, X, S, d, Y, V, hc, _, mx, _, elem⟩ := get i i f hf
    obtain ⟨y, _, hxy⟩ := elem.1.1.2.2 x ((ep_at_read_l hq hc mx.1).mp hx)
    exact (read u u i i x x hp hp).mpr ⟨hu, hu, f, hf, (h.identity i f hf x y hxy).symm ▸ hxy⟩
  · intro u v w huv hvw
    obtain ⟨i, x, _, hu, _⟩ := (tags.nodes u).mp (bound u v huv).1
    obtain ⟨j, y, _, hv, _⟩ := (tags.nodes v).mp (bound u v huv).2
    obtain ⟨k, z, _, hw, _⟩ := (tags.nodes w).mp (bound v w hvw).2
    obtain ⟨f, hf, hxy⟩ := ((read u v i j x y hu hv).mp huv).2.2
    obtain ⟨g, hg, hyz⟩ := ((read v w j k y z hv hw).mp hvw).2.2
    obtain ⟨t, ht⟩ := h.map_l hZF (h.order.trans i j k (h.map_bound_l hZF hf) (h.map_bound_l hZF hg))
    exact (read u w i k x z hu hw).mpr ⟨(bound u v huv).1, (bound v w hvw).2, t, ht,
      h.comp i j k f g t hf hg ht x y z hxy hyz⟩
  · intro u i j hui hij
    obtain ⟨x, hp, hx⟩ := tags.label_l hui
    obtain ⟨f, hf⟩ := h.map_l hZF ((ls i j).mp hij).2.2
    obtain ⟨c, X, S, d, Y, V, hc, hd, mx, my, elem⟩ := get i j f hf
    obtain ⟨y, hy, hxy⟩ := elem.1.1.2.2 x ((ep_at_read_l hq hc mx.1).mp hx)
    obtain ⟨v, hvA, hv, hvj⟩ := node j y (order.bound i j hij).2 ⟨d, Y, V, hd, my.1, hy⟩
    exact ⟨v, hvj, (read u v i j x y hp hv).mpr ⟨(tags.projection.bound_l hui).1, hvA, f, hf, hxy⟩⟩
  · intro u v w j hvj hwj huv huw
    obtain ⟨i, x, _, hu, _⟩ := (tags.nodes u).mp (bound u v huv).1
    obtain ⟨y, hv, _⟩ := tags.label_l hvj
    obtain ⟨z, hw, _⟩ := tags.label_l hwj
    obtain ⟨f, hf, hxy⟩ := ((read u v i j x y hu hv).mp huv).2.2
    obtain ⟨_, _, _, _, _, _, _, _, _, _, elem⟩ := get i j f hf
    have eq := elem.1.1.1.2 x y z hxy ((arrow i j x z f hf).mp ((read u w i j x z hu hw).mp huw).2.2)
    exact I.unique (eq ▸ hv) hw
  · intro u v w i hui hvi huw hvw
    obtain ⟨x, hu, _⟩ := tags.label_l hui
    obtain ⟨y, hv, _⟩ := tags.label_l hvi
    obtain ⟨j, z, _, hw, _⟩ := (tags.nodes w).mp (bound u w huw).2
    obtain ⟨f, hf, hxz⟩ := ((read u w i j x z hu hw).mp huw).2.2
    obtain ⟨_, _, _, _, _, _, _, _, _, _, elem⟩ := get i j f hf
    have eq := elem.1.2 x y z hxz ((arrow i j y z f hf).mp ((read v w i j y z hv hw).mp hvw).2.2)
    exact I.unique (eq ▸ hu) hv
  · intro u v huv
    obtain ⟨huA, hvA, i, x, y, hu, hv, _⟩ := (tags.relations u v).mp huv
    exact ⟨i, (tags.index u i x hu).mpr huA, (tags.index v i y hv).mpr hvA⟩
  · intro u v i a b j hui hvi haj hbj hua hvb
    obtain ⟨x, hu, _⟩ := tags.label_l hui
    obtain ⟨y, hv, _⟩ := tags.label_l hvi
    obtain ⟨z, ha, _⟩ := tags.label_l haj
    obtain ⟨t, hb, _⟩ := tags.label_l hbj
    obtain ⟨f, hf, hxz⟩ := ((read u a i j x z hu ha).mp hua).2.2
    obtain ⟨c, X, S, d, Y, V, hc, hd, mx, my, elem⟩ := get i j f hf
    have hyt := (arrow i j y t f hf).mp ((read v b i j y t hv hb).mp hvb).2.2
    have old : Rd_entry_d u v R ↔ Rd_entry_d x y S := (tags.relation_l hu hv).trans
      (⟨And.right ∘ And.right, fun hr => ⟨(tags.projection.bound_l hui).1, (tags.projection.bound_l hvi).1, hr⟩⟩ :
        (M.mem u A ∧ M.mem v A ∧ Ep_rel_d Q i x y) ↔ Ep_rel_d Q i x y) |>.trans (ep_rel_read_l hq hc mx.1)
    have next : Rd_entry_d a b R ↔ Rd_entry_d z t V := (tags.relation_l ha hb).trans
      (⟨And.right ∘ And.right, fun hr => ⟨(tags.projection.bound_l haj).1, (tags.projection.bound_l hbj).1, hr⟩⟩ :
        (M.mem a A ∧ M.mem b A ∧ Ep_rel_d Q j z t) ↔ Ep_rel_d Q j z t) |>.trans (ep_rel_read_l hq hd my.1)
    exact old.trans ((elem.relation_l I hZF hω mx my hxz hyt).trans next.symm)

end YesMetaZFC.SetTheory.LargeCardinal
