import YesMetaZFC.SetTheory.LargeCardinal.IterationTree
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Cone

/-! # 树的极限条件给出实际直接极限证书

把各前驱模型通过已存嵌入识别为目标中的像。带指标的这些像组成实际
定向系统，其取值图覆盖目标；一般相容锥定理于是识别同一个目标为直接极限。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_image_d (G i δ y : M.Domain) : Prop := ∃ f, It_map_d G i δ f ∧ ∃ x, Rd_entry_d x y f
def it_image_m {d} (G i δ y : Term d) : Formula 1 d := .existsE
  (.conj (it_map_m G.weaken i.weaken δ.weaken .newest) (.existsE (rd_entry_m .newest y.weaken.weaken (.bound 1))))
derive_free_closed it_image_m

theorem it_image_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G i δ y : Term d) :
    Formula.satisfies ρ (it_image_m G i δ y) ↔ It_image_d (G.eval ρ) (i.eval ρ) (δ.eval ρ) (y.eval ρ) := by
  simp only [it_image_m, It_image_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    it_map_sat_l hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem it_branch_limit_l (hZF : M.Models ZF) {ω α T Q G δ : M.Domain}
    (h : It_diagram_d hZF ω α T Q G) (hδ : M.mem δ α) (cover : It_limit_d T Q G δ) :
    ∃ c Y V J L A p B R e, Rd_entry_d δ c Q ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c Y V ∧
      Di_system_d J L A p B R ∧ Di_limit_d A p B R e Y V ∧
      (∀ i, M.mem i J ↔ M.mem i δ ∧ Rd_entry_d i δ T) ∧
      (∀ i j, Rd_entry_d i j L ↔ M.mem i J ∧ M.mem j J ∧ Rd_entry_d i j T) ∧
      (∀ a, M.mem a A ↔ ∃ i, M.mem i J ∧ ∃ y, M.mem y Y ∧ KPair_d M a i y ∧ It_image_d G i δ y) ∧
      (∀ a i y, Rd_entry_d a i p → Rd_entry_d a y e → KPair_d M a i y) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, Y, V, hc, model⟩ := h.model_l hZF hδ
  let φ : UnarySchema 2 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨J, js⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases δ (fun _ => T), fun _ => δ⟩ δ
  have index i : M.mem i J ↔ M.mem i δ ∧ Rd_entry_d i δ T :=
    (js i).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 ..)
  have inside i (hi : M.mem i J) := h.order.ordinal.transitive δ hδ i ((index i).mp hi).1
  let ψ : BinarySchema 1 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
  obtain ⟨L, _, ls⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ⟨fun _ => T, fun _ => T⟩ J
  have order i j : Rd_entry_d i j L ↔ M.mem i J ∧ M.mem j J ∧ Rd_entry_d i j T :=
    (ls i j).trans (and_congr_right fun _ => and_congr_right fun _ => rd_entry_sat_l hZF.1 ..)
  have directed : Di_order_d J L := ⟨fun i hi => (order i i).mpr ⟨hi, hi, h.order.refl i (inside i hi)⟩,
    fun i j k hij hjk => (order i k).mpr ⟨((order i j).mp hij).1, ((order j k).mp hjk).2.1,
      h.order.trans i j k ((order i j).mp hij).2.2 ((order j k).mp hjk).2.2⟩,
    fun i j hij => ⟨((order i j).mp hij).1, ((order i j).mp hij).2.1⟩, fun i j hi hj => by
      rcases h.order.chain i j δ ((index i).mp hi).2 ((index j).mp hj).2 with hij | hji
      · exact ⟨j, hj, (order i j).mpr ⟨hi, hj, hij⟩, (order j j).mpr ⟨hj, hj, h.order.refl j (inside j hj)⟩⟩
      · exact ⟨i, hi, (order i i).mpr ⟨hi, hi, h.order.refl i (inside i hi)⟩, (order j i).mpr ⟨hj, hi, hji⟩⟩⟩
  have mono i j (hij : Rd_entry_d i j L) y (hy : It_image_d G i δ y) : It_image_d G j δ y := by
    obtain ⟨hi, hj, hij⟩ := (order i j).mp hij
    obtain ⟨f, hf, x, hxy⟩ := hy
    obtain ⟨g, hg⟩ := h.map_l hZF hij
    obtain ⟨k, hk⟩ := h.map_l hZF ((index j).mp hj).2
    obtain ⟨b, X, R, hb, mx⟩ := h.model_l hZF (inside i hi)
    obtain ⟨d, Z, S, hd, mz⟩ := h.model_l hZF (inside j hj)
    have ff := h.elementary i δ f b X R c Y V hf hb hc mx model
    have gg := h.elementary i j g b X R d Z S hg hb hd mx mz
    have kk := h.elementary j δ k d Z S c Y V hk hd hc mz model
    obtain ⟨z, hz, hxz⟩ := gg.1.1.2.2 x (ff.1.1.input_mem_of_pairMember hxy)
    obtain ⟨y', _, hzy⟩ := kk.1.1.2.2 z hz
    exact ⟨k, hk, z, ff.1.1.1.2 x y' y (h.comp i j δ g k f hg hk hf x z y' hxz hzy) hxy ▸ hzy⟩
  obtain ⟨D, hd⟩ := ZF.exists_cartesianProduct hZF I J Y
  let ρ : Env M 4 := ⟨Fin.cases J (Fin.cases Y (Fin.cases G (fun _ => δ))), fun _ => δ⟩
  let θ : UnarySchema 4 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3)
      (.conj (kpair_m (.bound 2) (.bound 1) .newest) (it_image_m (.bound 5) (.bound 1) (.bound 6) .newest))) }
  obtain ⟨A, as⟩ := ZF.separation_exists_d hZF θ ρ D
  have nodes a : M.mem a A ↔ ∃ i, M.mem i J ∧ ∃ y, M.mem y Y ∧ KPair_d M a i y ∧ It_image_d G i δ y := by
    have sat : θ.denote ρ a ↔ ∃ i, M.mem i J ∧ ∃ y, M.mem y Y ∧ KPair_d M a i y ∧ It_image_d G i δ y := by
      simp only [θ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
        kpair_sat_l M hZF.1, it_image_sat_l hZF.1]; rfl
    exact (as a).trans ((and_congr_right fun _ => sat).trans ⟨And.right,
      fun ⟨i, hi, y, hy, hp, image⟩ => ⟨(hd a).mpr ⟨i, hi, y, hy, hp⟩, i, hi, y, hy, hp, image⟩⟩)
  let first : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  let second : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) .newest (.bound 1)) }
  let η : Env M 0 := ⟨Fin.elim0, fun _ => Y⟩
  have fval a i : first.denote η a i ↔ ∃ y, KPair_d M a i y := by
    simp only [first, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  have sval a y : second.denote η a y ↔ ∃ i, KPair_d M a i y := by
    simp only [second, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  obtain ⟨p, hp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I first η (source := A) (target := J)
    (fun a ha => by obtain ⟨i, _, y, _, pair, _⟩ := (nodes a).mp ha; exact ⟨i, (fval a i).mpr ⟨y, pair⟩⟩)
    (fun a _ i j hi hj => by
      obtain ⟨x, hx⟩ := (fval a i).mp hi
      obtain ⟨y, hy⟩ := (fval a j).mp hj
      exact (kpair_injective_l M hx hy).1)
    (fun a i ha hi => by
      obtain ⟨j, hj, y, _, pair, _⟩ := (nodes a).mp ha
      obtain ⟨x, pair'⟩ := (fval a i).mp hi
      exact (kpair_injective_l M pair pair').1 ▸ hj)
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I second η (source := A) (target := Y)
    (fun a ha => by obtain ⟨i, _, y, _, pair, _⟩ := (nodes a).mp ha; exact ⟨y, (sval a y).mpr ⟨i, pair⟩⟩)
    (fun a _ x y hx hy => by
      obtain ⟨i, hi⟩ := (sval a x).mp hx
      obtain ⟨j, hj⟩ := (sval a y).mp hy
      exact (kpair_injective_l M hi hj).2)
    (fun a y ha hy => by
      obtain ⟨i, _, x, hx, pair, _⟩ := (nodes a).mp ha
      obtain ⟨j, pair'⟩ := (sval a y).mp hy
      exact (kpair_injective_l M pair pair').2 ▸ hx)
  have read a i y (hai : Rd_entry_d a i p) (hay : Rd_entry_d a y e) : KPair_d M a i y := by
    obtain ⟨x, hx⟩ := (fval a i).mp ((ps a i).mp hai).2
    obtain ⟨j, hj⟩ := (sval a y).mp ((es a y).mp hay).2
    exact (kpair_injective_l M hx hj).2 ▸ hx
  have node i y (hi : M.mem i J) (hy : M.mem y Y) (image : It_image_d G i δ y) : ∃ a, Rd_entry_d a i p ∧ Rd_entry_d a y e := by
    obtain ⟨a, pair⟩ := I.total i y
    have ha := (nodes a).mpr ⟨i, hi, y, hy, pair, image⟩
    exact ⟨a, (ps a i).mpr ⟨ha, (fval a i).mpr ⟨y, pair⟩⟩, (es a y).mpr ⟨ha, (sval a y).mpr ⟨i, pair⟩⟩⟩
  have value a i y (hai : Rd_entry_d a i p) (hay : Rd_entry_d a y e) : It_image_d G i δ y := by
    obtain ⟨j, _, x, _, pair, image⟩ := (nodes a).mp (hp.input_mem_of_pairMember hai)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair (read a i y hai hay)
    exact image
  obtain ⟨B, R, system, bs, rs⟩ := di_cone_system_l (V := V) hZF directed
    (fn0_of_function_l (ZF.modelsKP hZF) hp) (fn0_of_function_l (ZF.modelsKP hZF) he)
    (fun a b i y ha hb hay hby => kpair_unique_l M hZF.1 (read a i y ha hay) (read b i y hb hby))
    (fun a i j y hai hij hay => node j y ((order i j).mp hij).2.1 (he.output_mem_of_pairMember hay)
      (mono i j hij y (value a i y hai hay)))
  have range y : M.mem y Y ↔ ∃ a, Rd_entry_d a y e := by
    constructor
    · intro hy
      obtain ⟨i, hi, hiδ, f, hf, x, hxy⟩ := cover c Y V hc model.1 y hy
      obtain ⟨a, _, hay⟩ := node i y ((index i).mpr ⟨hi, hiδ⟩) hy ⟨f, hf, x, hxy⟩
      exact ⟨a, hay⟩
    · exact fun ⟨_, hay⟩ => he.output_mem_of_pairMember hay
  exact ⟨c, Y, V, J, L, A, p, B, R, e, hc, model, system,
    di_cone_limit_l system (fn0_of_function_l (ZF.modelsKP hZF) he) range bs rs model.2.2.2 model.2.2.1,
    index, order, nodes, read⟩

end YesMetaZFC.SetTheory.LargeCardinal
