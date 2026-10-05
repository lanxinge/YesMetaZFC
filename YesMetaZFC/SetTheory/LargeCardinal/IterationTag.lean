import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagram
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystemSyntax
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Stages
import YesMetaZFC.SetTheory.KP.Transitive

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
    (h : It_diagram_d hZF ω α T Q G) : ∃ D, Fn0_d α D Q := by
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
