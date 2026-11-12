import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.SetTheory.KP.Transitive
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch

/-! # 树枝上各模型的带标号并

每个元素保留原模型指标与实际取值。统一界取模型列的传递包络，随后用
分离构造载体、指标图和分量关系；这里还没有引入任何极限或良基性条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure It_tag_d (B Q A p R : M.Domain) : Prop where
  nodes : ∀ u, M.mem u A ↔ ∃ i x, M.mem i B ∧ KPair_d M u i x ∧ Ep_at_d Q i x
  projection : Fn0_d A B p
  index : ∀ u i x, KPair_d M u i x → (Rd_entry_d u i p ↔ M.mem u A)
  relations : ∀ u v, Rd_entry_d u v R ↔ M.mem u A ∧ M.mem v A ∧
    ∃ i x y, KPair_d M u i x ∧ KPair_d M v i y ∧ Ep_rel_d Q i x y

theorem It_tag_d.at_l {B Q A p R u i x : M.Domain} (h : It_tag_d B Q A p R)
    (hu : M.mem u A) (hp : KPair_d M u i x) : Ep_at_d Q i x := by
  obtain ⟨j, y, _, hp', hy⟩ := (h.nodes u).mp hu
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
  exact hy

theorem It_tag_d.label_l {B Q A p R u i : M.Domain} (h : It_tag_d B Q A p R)
    (hui : Rd_entry_d u i p) : ∃ x, KPair_d M u i x ∧ Ep_at_d Q i x := by
  obtain ⟨j, x, _, hp, hx⟩ := (h.nodes u).mp (h.projection.bound_l hui).1
  have huj := (h.index u j x hp).mpr (h.projection.bound_l hui).1
  have eq := h.projection.2.2 u (h.projection.bound_l hui).1 j (h.projection.bound_l huj).2
    i (h.projection.bound_l hui).2 huj hui
  exact ⟨x, eq ▸ hp, eq ▸ hx⟩

theorem It_tag_d.relation_l {B Q A p R u v i x y : M.Domain} (h : It_tag_d B Q A p R)
    (hu : KPair_d M u i x) (hv : KPair_d M v i y) :
    Rd_entry_d u v R ↔ M.mem u A ∧ M.mem v A ∧ Ep_rel_d Q i x y := by
  refine (h.relations u v).trans ⟨fun ⟨huA, hvA, j, a, b, hu', hv', hr⟩ => ?_,
    fun ⟨huA, hvA, hr⟩ => ⟨huA, hvA, i, x, y, hu, hv, hr⟩⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu'
  have eq := (kpair_injective_l M hv hv').2
  exact ⟨huA, hvA, eq ▸ hr⟩

theorem It_diagram_d.family_l (hZF : M.Models ZF) {ω α T Q G : M.Domain}
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) : ∃ D, Fn0_d α D Q := by
  obtain ⟨D, hd⟩ := ZF.exists_range_of_setFunction hZF (kp_pair_l (ZF.modelsKP hZF)) h.model_function h.model_domain
  exact ⟨D, fn0_of_function_l (ZF.modelsKP hZF) ⟨h.model_function, h.model_domain, fun i hi => by
    obtain ⟨c, hc⟩ := (h.model_domain i).mp hi
    exact ⟨c, (hd c).mpr ⟨i, hc⟩, hc⟩⟩⟩

theorem it_tags_l (hZF : M.Models ZF) (B Q : M.Domain) : ∃ A p R, It_tag_d B Q A p R := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨H, ht, hQ⟩ := KPi.transitive_cover_l (ZF.models_kpi_l hZF) Q
  have bound i x (hx : Ep_at_d Q i x) : M.mem x H := by
    obtain ⟨c, X, R, hi, hc, hx⟩ := hx
    have hCH := (rd_entry_transitive_l ht hQ hi).2
    obtain ⟨a, hac, hXa⟩ := (kpair_union_l M hc X).mpr (Or.inl rfl)
    exact ht X (ht a (ht c hCH a hac) X hXa) x hx
  obtain ⟨D, hd⟩ := ZF.exists_cartesianProduct hZF I B H
  let φ : UnarySchema 2 := { body := .existsE (.existsE (.conj (.mem (.bound 1) (.bound 3))
    (.conj (kpair_m (.bound 2) (.bound 1) .newest) (ep_at_m (.bound 4) (.bound 1) .newest)))) }
  let ρ : Env M 2 := ⟨Fin.cases B (fun _ => Q), fun _ => Q⟩
  have sat u : φ.denote ρ u ↔ ∃ i x, M.mem i B ∧ KPair_d M u i x ∧ Ep_at_d Q i x := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, kpair_sat_l M hZF.1, ep_at_sat_l hZF.1]; rfl
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF φ ρ D
  have nodes u : M.mem u A ↔ ∃ i x, M.mem i B ∧ KPair_d M u i x ∧ Ep_at_d Q i x :=
    (ha u).trans ((and_congr_right fun _ => sat u).trans ⟨And.right,
      fun ⟨i, x, hi, hp, hx⟩ => ⟨(hd u).mpr ⟨i, hi, x, bound i x hx, hp⟩, i, x, hi, hp, hx⟩⟩)
  let ψ : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  let η : Env M 0 := ⟨Fin.elim0, fun _ => Q⟩
  have psat u i : ψ.denote η u i ↔ ∃ x, KPair_d M u i x := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  obtain ⟨p, hp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := A) (target := B)
    (fun u hu => by obtain ⟨i, x, _, h, _⟩ := (nodes u).mp hu; exact ⟨i, (psat u i).mpr ⟨x, h⟩⟩)
    (fun u _ i j hi hj => by
      obtain ⟨x, hx⟩ := (psat u i).mp hi
      obtain ⟨y, hy⟩ := (psat u j).mp hj
      exact (kpair_injective_l M hx hy).1)
    (fun u i hu hi => by
      obtain ⟨j, x, hj, hp, _⟩ := (nodes u).mp hu
      obtain ⟨y, hp'⟩ := (psat u i).mp hi
      exact (kpair_injective_l M hp hp').1 ▸ hj)
  let χ : BinarySchema 1 := { body := .existsE (.existsE (.existsE (.conj
    (kpair_m (.bound 4) (.bound 2) (.bound 1)) (.conj (kpair_m (.bound 3) (.bound 2) .newest)
      (ep_rel_m (.bound 5) (.bound 2) (.bound 1) .newest))))) }
  obtain ⟨R, _, rs⟩ := ZF.exists_setRelationOn_of_denote hZF I χ ⟨fun _ => Q, fun _ => Q⟩ A
  refine ⟨A, p, R, nodes, fn0_of_function_l (ZF.modelsKP hZF) hp,
    fun u i x hc => ⟨hp.input_mem_of_pairMember, fun hu => (ps u i).mpr ⟨hu, (psat u i).mpr ⟨x, hc⟩⟩⟩, ?_⟩
  intro u v
  simpa only [χ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hZF.1, ep_rel_sat_l hZF.1] using! rs u v

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原模型与带标号分量的完整内部同构 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem it_tag_iso_l (hZF : M.Models ZF) {ω B Q A p R D H i c X S d Y V : M.Domain}
    (hω : M.IsOmega ω) (h : It_tag_d B Q A p R) (hq : Fn0_d D H Q)
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i d Y V)
    (hc : Rd_entry_d i c Q) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X S) :
    ∃ e u, Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω d c Y X e ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y u ∧
      (∀ a x, Rd_entry_d a x e ↔ M.mem a Y ∧ KPair_d M a i x) ∧
      ∀ x a, Rd_entry_d x a u ↔ M.mem a Y ∧ KPair_d M a i x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨a, ha⟩ := stage.1.2.1
  have hi := (h.projection.bound_l ((stage.2.1 a).mp ha).2).2
  let φ : BinarySchema 1 := { body := kpair_m (.bound 1) (.bound 2) .newest }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have sat a x : φ.denote ρ a x ↔ KPair_d M a i x := kpair_sat_l M hZF.1 ..
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := X)
    (fun a ha => by
      obtain ⟨x, hp, _⟩ := h.label_l (((stage.2.1 a).mp ha).2)
      exact ⟨x, (sat a x).mpr hp⟩)
    (fun a _ x y hx hy => (kpair_injective_l M ((sat a x).mp hx) ((sat a y).mp hy)).2)
    (fun a x ha hx => (ep_at_read_l hq hc model.1).mp (h.at_l (((stage.2.1 a).mp ha).1) ((sat a x).mp hx)))
  have read a x : Rd_entry_d a x e ↔ M.mem a Y ∧ KPair_d M a i x :=
    (es a x).trans (and_congr_right fun _ => sat a x)
  have bij : M.IsSetBijectionFromTo I e Y X := by
    refine ⟨⟨he, fun a b x ha hb => I.unique (((read a x).mp ha).2) (((read b x).mp hb).2)⟩, fun x hx => ?_⟩
    obtain ⟨a, hp⟩ := I.total i x
    have ha := (h.nodes a).mpr ⟨i, x, hi, hp, c, X, S, hc, model.1, hx⟩
    have haY := (stage.2.1 a).mpr ⟨ha, (h.index a i x hp).mpr ha⟩
    exact ⟨a, haY, (read a x).mpr ⟨haY, hp⟩⟩
  have rel a b x y (ha : Rd_entry_d a x e) (hb : Rd_entry_d b y e) : Rd_entry_d a b V ↔ Rd_entry_d x y S := by
    obtain ⟨haY, hp⟩ := (read a x).mp ha
    obtain ⟨hbY, hq'⟩ := (read b y).mp hb
    have first : Rd_entry_d a b V ↔ Rd_entry_d a b R := (stage.2.2 a b).trans
      ⟨And.right ∘ And.right, fun hr => ⟨haY, hbY, hr⟩⟩
    have second : Rd_entry_d a b R ↔ Ep_rel_d Q i x y := (h.relation_l hp hq').trans
      ⟨And.right ∘ And.right, fun hr => ⟨((stage.2.1 a).mp haY).1, ((stage.2.1 b).mp hbY).1, hr⟩⟩
    exact first.trans (second.trans (ep_rel_read_l hq hc model.1))
  obtain ⟨u, hu, us⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  exact ⟨e, u, smap_of_iso_l I hZF hω stage.1 model bij rel,
    smap_of_iso_l I hZF hω model stage.1 hu (fun x y a b ha hb =>
      (rel a b x y ((us x a).mp ha) ((us y b).mp hb)).symm), read,
    fun x a => (us x a).trans (read a x)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 树枝上的实际定向系统

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
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G)
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
