import YesMetaZFC.SetTheory.LargeCardinal.Extender.NormalSource
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.SetTheory.Collapse.RelationMap

/-! # 源内坐标代表与坐标原子

坐标函数 s↦s(i) 在任意实际源中构造。坐标重排严格拉回这些函数；
扩展器的坐标等号和序条件随后精确读成商中的等号与隶属。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Ep_coord_d (κ D i f : M.Domain) : Prop := Fn0_d D κ f ∧
  ∀ s x, Rd_entry_d s x f ↔ M.mem s D ∧ Rd_entry_d i x s

def ep_coord_m {d} (κ D i f : Term d) : Formula 1 d := .conj (fn0_m D κ f)
  (.forallE (.forallE (.iff (rd_entry_m (.bound 1) .newest f.weaken.weaken)
    (.conj (.mem (.bound 1) D.weaken.weaken) (rd_entry_m i.weaken.weaken .newest (.bound 1))))))
derive_free_closed ep_coord_m

theorem ep_coord_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ D i f : Term d) :
    Formula.satisfies ρ (ep_coord_m κ D i f) ↔ Ep_coord_d (κ.eval ρ) (D.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [ep_coord_m, Ep_coord_d, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, rd_entry_sat_l hE,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem Ep_source_d.coordinate_l (hZF : M.Models ZF) {ω κ K X R n D i : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D) (hi : M.mem i n) :
    ∃ f, M.mem f X ∧ Ep_coord_d κ D i f := by
  obtain ⟨c, code⟩ := source.code
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 2) .newest (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have sat s x : φ.denote ρ s x ↔ Rd_entry_d i x s := rd_entry0_sat_l hZF.1 ..
  obtain ⟨f, hfX, hf, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory
    φ (rd_entry0_delta_l ..) ρ
    (fun _ => source.transitive ω source.omega_mem i (source.omega.transitive (ZF.modelsKP hZF) n hn i hi))
    (source.space_mem_l hZF hn hD) source.cardinal_mem (fun s hs => by
      obtain ⟨x, hx, hix⟩ := ((hD s).mp hs).2.1 i hi
      exact ⟨x, hx, (sat s x).mpr hix⟩)
  have entry s x (hsx : Rd_entry_d s x f) := (sat s x).mp (select s x hsx)
  refine ⟨f, hfX, hf,
    fun s x => ⟨fun h => ⟨(hf.bound_l h).1, entry s x h⟩, ?_⟩⟩
  rintro ⟨hs, hix⟩
  obtain ⟨y, _, hsy⟩ := hf.2.1 s hs
  exact (fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hs)).1.2 i y x (entry s y hsy) hix ▸ hsy

theorem Ep_coord_d.pull_l {κ X m n D E r i j f g : M.Domain}
    (hκX : M.MemberSubset κ X) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E)
    (hr : Fn0_d m n r) (hij : Rd_entry_d i j r) (hf : Ep_coord_d κ D i f) (hg : Ep_coord_d κ E j g) :
    Ep_pull_d κ X m n r f g := by
  refine ⟨⟨D, hD, hf.1.mono_target_l hκX⟩, ⟨E, hE, hg.1.mono_target_l hκX⟩, fun s t hs ht x => ?_⟩
  exact (hg.2 s x).trans ((and_congr Iff.rfl (ht.value_l hr hs hij).symm).trans
    ⟨fun h => (hf.2 t x).mpr ⟨(hD t).mpr ht.1, h.2⟩,
      fun h => ⟨(hE s).mpr hs, ((hf.2 t x).mp h).2⟩⟩)

theorem ep_coordinate_atoms_l (hZF : M.Models ZF) {ω κ K X R L F n D a U i j α β f g : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (hn : M.mem n ω) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D)
    (haU : Rd_entry_d a U F) (hi : Rd_entry_d i α a) (hj : Rd_entry_d j β a)
    (hf : Ep_coord_d κ D i f) (hg : Ep_coord_d κ D j g) :
    (Rp_eq_d X U f g ↔ α = β) ∧ (Rp_rel_d (kp_pair_l (ZF.modelsKP hZF)) X U R f g ↔ M.mem α β) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, code⟩ := source.code
  have ultra := family.at_l hZF.1 haU ha hD
  have part (b : Bool) : (∃ A, M.mem A U ∧ ∀ s, M.mem s A → Rp_atom_d I b X R f g s) ↔
      if b then α = β else M.mem α β := by
    let ρ : Env M 3 := ⟨Fin.cases κ (Fin.cases i (fun _ => j)), fun _ => κ⟩
    let φ : UnarySchema 3 := { body := ea_test_m b (.bound 1) (.bound 2) (.bound 3) .newest }
    have hnat t (ht : M.mem t n) := source.transitive ω source.omega_mem t (source.omega.transitive (ZF.modelsKP hZF) n hn t ht)
    obtain ⟨B, hBX, bs⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory
      φ (ea_test_delta_l ..) ρ (Fin.cases source.cardinal_mem (Fin.cases (hnat i (ha.bound_l hi).1)
        (fun _ => hnat j (ha.bound_l hj).1))) (source.space_mem_l hZF hn hD)
    have read s : M.mem s B ↔ M.mem s D ∧ Ea_test_d b κ i j s :=
      (bs s).trans (and_congr_right fun _ => ea_test_sat_l hZF.1 ..)
    obtain ⟨B', bs', value⟩ := atoms b n a U i j α β hn ha haU hi hj
    have eB := hZF.1.eq_of_same_members B' B fun s => (bs' s).trans ((and_congr (hD s).symm Iff.rfl).trans (read s).symm)
    subst B'
    have point s (hs : M.mem s D) : Rp_atom_d I b X R f g s ↔ Ea_test_d b κ i j s := by
      obtain ⟨x, hx, hsx⟩ := hf.1.2.1 s hs
      obtain ⟨y, hy, hsy⟩ := hg.1.2.1 s hs
      have hix := ((hf.2 s x).mp hsx).2
      have hjy := ((hg.2 s y).mp hsy).2
      rw [ea_test_read_l b ((hD s).mp hs) hix hjy]
      have hxX := source.transitive κ source.cardinal_mem x hx
      have hyX := source.transitive κ source.cardinal_mem y hy
      constructor
      · rintro ⟨x', _, y', _, hsx', hsy', h⟩
        have ex := (fn0_function_l (ZF.modelsKP hZF) hf.1).1.2 s x' x hsx' hsx
        have ey := (fn0_function_l (ZF.modelsKP hZF) hg.1).1.2 s y' y hsy' hsy
        subst x' y'
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        · exact ((code.2 x y).mp h).2.2
        · exact h
      · intro h
        refine ⟨x, hxX, y, hyX, hsx, hsy, ?_⟩
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        · exact (code.2 x y).mpr ⟨hxX, hyX, h⟩
        · exact h
    apply Iff.trans ?_ value
    exact ⟨fun ⟨A, hAU, hA⟩ => ultra.upward A B hAU hBX (fun s hs => ((read s).mp hs).1)
      (fun s hs => (read s).mpr ⟨ultra.base.bounds A hAU s hs, (point s (ultra.base.bounds A hAU s hs)).mp (hA s hs)⟩),
      fun hB => ⟨B, hB, fun s hs => (point s ((read s).mp hs).1).mpr ((read s).mp hs).2⟩⟩
  exact ⟨(rp_atom_eq_l I (R := R)).symm.trans (part true), part false⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 扩展器支撑在同一商极限中的坐标像

任意支撑中的同一坐标给出相同极限元素；坐标间的等号和序恰好成为
极限中的等号和隶属。此处尚不使用整体良基性或传递坍塌。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_seed_d (κ L q α E : M.Domain) : Prop := ∃ n a i D f,
  Fn0_d n L a ∧ Rd_entry_d i α a ∧ Ep_space_d κ n D ∧ Ep_coord_d κ D i f ∧ Ep_repr_d q a f E

def ep_seed_m {d} (κ L q α E : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (fn0_m (.bound 4) (w L) (.bound 3))
      (.conj (rd_entry_m (.bound 2) (w α) (.bound 3))
        (.conj (ep_space_m (w κ) (.bound 4) (.bound 1))
          (.conj (ep_coord_m (w κ) (.bound 1) (.bound 2) .newest)
            (ep_repr_m (w q) (.bound 3) .newest (w E))))))))))
derive_free_closed ep_seed_m

theorem ep_seed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L q α E : Term d) :
    Formula.satisfies ρ (ep_seed_m κ L q α E) ↔
      Ep_seed_d (κ.eval ρ) (L.eval ρ) (q.eval ρ) (α.eval ρ) (E.eval ρ) := by
  simp only [ep_seed_m, Ep_seed_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, rd_entry_sat_l hE, ep_space_sat_l hE, ep_coord_sat_l hE, ep_repr_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q C W : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_seed_exists_l (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {α : M.Domain} (hα : M.mem α L) : ∃ E, M.mem E C ∧ Ep_seed_d κ L q α E := by
  obtain ⟨n, ⟨z, hz, hzn⟩, hn⟩ := source.omega.exists_ordinalOne_mem
  obtain ⟨a, ha, spec⟩ := ZF.exists_constantFunction hZF I (source := n) hα
  have single i (hi : M.mem i n) : i = z := ((hzn i).mp hi).elim
    (fun hi => (hz i hi).elim) (hZF.1.eq_of_same_members i z)
  have haJ := (h.indices a).mpr ⟨n, hn, fn0_of_function_l (ZF.modelsKP hZF) ha,
    fun i j x hi hj => (single i (ha.input_mem_of_pairMember hi)).trans (single j (ha.input_mem_of_pairMember hj)).symm⟩
  obtain ⟨D, _, hD⟩ := source.space_l hZF hn
  obtain ⟨f, hfX, hf⟩ := source.coordinate_l hZF hn hD hzn.predecessor_mem
  obtain ⟨E, hEC, value⟩ := ep_repr_exists_l hZF family h limit haJ (fn0_of_function_l (ZF.modelsKP hZF) ha)
    hD hfX (hf.1.mono_target_l (source.transitive κ source.cardinal_mem))
  exact ⟨E, hEC, n, a, z, D, f, fn0_of_function_l (ZF.modelsKP hZF) ha,
    (spec z α).mpr ⟨hzn.predecessor_mem, rfl⟩, hD, hf, value⟩

/-- 把指定坐标代表送到任意包含原支撑的分量；坐标值不变。 -/
theorem ep_seed_move_l (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {a b n D i α f E : M.Domain} (ha : Fn0_d n L a) (hi : Rd_entry_d i α a)
    (hD : Ep_space_d κ n D) (hf : Ep_coord_d κ D i f) (value : Ep_repr_d q a f E)
    (hab : Rd_entry_d a b O) : ∃ m D' j g, M.mem m ω ∧ Fn0_d m L b ∧ Rd_entry_d j α b ∧
      Ep_space_d κ m D' ∧ M.mem g X ∧ Ep_coord_d κ D' j g ∧ Ep_repr_d q b g E := by
  obtain ⟨_, hbJ, r, n', m, hn, hm, hr, hb, hra⟩ := (h.order_spec a b).mp hab
  have en := hra.1.domain_eq_l hZF.1 ha
  subst n'
  obtain ⟨j, hjm, hij⟩ := hr.2.1 i (ha.bound_l hi).1
  obtain ⟨D', _, hD'⟩ := source.space_l hZF hm
  obtain ⟨g, hgX, hg⟩ := source.coordinate_l hZF hm hD' hjm
  obtain ⟨H, _, hv⟩ := ep_repr_exists_l hZF family h limit hbJ hb hD' hgX
    (hg.1.mono_target_l (source.transitive κ source.cardinal_mem))
  have eq := ep_repr_pull_l hZF h limit hn hm hr hb hra
    (Ep_coord_d.pull_l (source.transitive κ source.cardinal_mem) hD hD' hr hij hf hg) value hv
  exact ⟨m, D', j, g, hm, hb, (hra.value_l hr hb hij).mp hi, hD', hgX, hg, eq.symm ▸ hv⟩

theorem ep_seed_atoms_l (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (h : Ep_system_d I ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C W) {α β E H : M.Domain}
    (he : Ep_seed_d κ L q α E) (hh : Ep_seed_d κ L q β H) :
    (E = H ↔ α = β) ∧ (Rd_entry_d E H W ↔ M.mem α β) := by
  obtain ⟨n, a, i, D, f, ha, hi, hD, hf, he⟩ := he
  obtain ⟨m, b, j, D', g, hb, hj, hD', hg, hh⟩ := hh
  obtain ⟨v, _, hav, hbv⟩ := h.order.directed a b (he.index_l hZF h limit) (hh.index_l hZF h limit)
  obtain ⟨l, Q, i', f', hl, hv, hi', hQ, _, hf', he'⟩ := ep_seed_move_l hZF source family h limit ha hi hD hf he hav
  obtain ⟨l', Q', j', g', _, hv', hj', hQ', _, hg', hh'⟩ := ep_seed_move_l hZF source family h limit hb hj hD' hg hh hbv
  have el := hv'.domain_eq_l hZF.1 hv
  subst l'
  have eQ := hZF.1.eq_of_same_members Q' Q fun s => (hQ' s).trans (hQ s).symm
  subst Q'
  obtain ⟨U, hvU⟩ := family.total l v hl hv
  have left := ep_repr_atoms_l hZF family h limit hvU he' hh'
  have right := ep_coordinate_atoms_l hZF source family atoms hl hv hQ hvU hi' hj' hf' hg'
  exact ⟨left.1.trans right.1, left.2.trans right.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 正规性使坐标像对前驱封闭

先把任意前驱和坐标放进共同分量，再把前驱代表改为 κ 值函数。
正规性给出较小的末坐标；即使它重复旧坐标，也先覆盖到实际单射支撑，
再用源内协调律识别同一个极限元素。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_seed_down_l {ω κ K L X R F J O Z A p T S q C W α E H : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hκ : M.TransitiveSet κ)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (normal : En_source_d ω κ L X F) (h : Ep_system_d I ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C W) (seed : Ep_seed_d κ L q α E) (hHE : Rd_entry_d H E W) :
    ∃ β, M.mem β α ∧ Ep_seed_d κ L q β H := by
  obtain ⟨n₀, a, i₀, D₀, f₀, ha, hi₀, hD₀, hf₀, value₀⟩ := seed
  obtain ⟨v, hvH⟩ := (limit.range H).mp (limit.bounded H E hHE).1
  obtain ⟨b, B, hv, _⟩ := (h.nodes v).mp (limit.projection.bound_l hvH).1
  have hvb := (h.index v b B hv).mpr (limit.projection.bound_l hvH).1
  obtain ⟨c, hcJ, hac, hbc⟩ := h.order.directed a b (value₀.index_l hZF h limit) (h.projection.bound_l hvb).2
  obtain ⟨n, D, i, f, hn, hc, hi, hD, hfX, hf, value⟩ :=
    ep_seed_move_l hZF source family h limit ha hi₀ hD₀ hf₀ value₀ hac
  obtain ⟨w, hwc, hvw⟩ := h.diagram.total v b c hvb hbc
  obtain ⟨H₀, _, hwH₀⟩ := limit.projection.2.1 w (h.diagram.bound v w hvw).2
  have hwH : Rd_entry_d w H q := (limit.commute_l h.diagram hvw hvH hwH₀).symm ▸ hwH₀
  obtain ⟨B', hw, hat⟩ := h.toEp_graph_d.label_l hwc
  obtain ⟨_, hz⟩ := h.codes
  have models := h.components
  obtain ⟨o, Q, V, hco, component, model, hBQ⟩ := ep_at_model_l hZF models hat
  obtain ⟨m, D', U, G, r, Q', V', _, hc', hD', hcU, hG, md⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I md.code model
  have en := hc'.domain_eq_l hZF.1 hc
  subst m
  have eD := hZF.1.eq_of_same_members D' D (fun s => (hD' s).trans (hD s).symm)
  subst D'
  obtain ⟨g, hgB⟩ := (md.map.range B').mp hBQ
  have hg := (hG g).mp (md.map.projection.input_mem_of_pairMember hgB)
  have ultra := family.at_l hZF.1 hcU hc hD
  have old : Ep_repr_d q c g H := ⟨w, B', hw, md.map.representative_l I ultra.base hgB, hwH⟩
  obtain ⟨z, _, hzω⟩ := source.omega.1.1
  obtain ⟨o₀, code⟩ := source.code
  have gBelow := (ep_repr_atoms_l hZF family h limit hcU old value).2.mp hHE
  obtain ⟨g', hg'X, hg', eqg⟩ := rs_bound_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hn hD) source.cardinal_mem hg.1 hg.2 (source.below z hzω) ultra.base.bounds (by
      obtain ⟨B, hBU, bound⟩ := gBelow
      exact ⟨B, hBU, fun s hs => by
        obtain ⟨x, _, y, _, hsx, hsy, hxy⟩ := bound s hs
        exact ⟨x, hκ y (hf.1.bound_l hsy).2 x ((code.2 x y).mp hxy).2.2, hsx⟩⟩)
  obtain ⟨H', _, value'⟩ := ep_repr_exists_l hZF family h limit hcJ hc hD hg'X
    (hg'.mono_target_l (source.transitive κ source.cardinal_mem))
  have eH := (ep_repr_atoms_l hZF family h limit hcU old value').1.mpr eqg
  have repr : Ep_repr_d q c g' H := eH.symm ▸ value'
  -- 回归关系的精确真值集属于源，因而可以继续施加源内协调律。
  obtain ⟨B₀, hB₀X, bs₀⟩ := sc_member_trace_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hn hD)
    (source.function_l hZF hg'X (hg'.mono_target_l (source.transitive κ source.cardinal_mem)))
    (source.function_l hZF hfX (hf.1.mono_target_l (source.transitive κ source.cardinal_mem)))
  have below := (ep_repr_atoms_l hZF family h limit hcU repr value).2.mp hHE
  have hB₀U : M.mem B₀ U := by
    obtain ⟨B, hBU, bound⟩ := below
    exact ultra.upward B B₀ hBU hB₀X (fun s hs => ((bs₀ s).mp hs).1)
      (fun s hs => (bs₀ s).mpr ⟨ultra.base.bounds B hBU s hs, bound s hs⟩)
  obtain ⟨m, b, V₀, β, B₁, hm, hmn, hb, hcb, hnβ, hβα, hbV, hB₁V, graph⟩ :=
    normal n c U D g' i α B₀ hn hc hcU hD hg'X hg' hi hB₀U (fun s hs x y hsx hiy => by
      obtain ⟨hsD, x', _, y', _, hsx', hsy', hxy⟩ := (bs₀ s).mp hs
      have ex := (fn0_function_l (ZF.modelsKP hZF) hg').1.2 s x' x hsx' hsx
      have ey := (fn0_function_l (ZF.modelsKP hZF) hf.1).1.2 s y' y hsy' ((hf.2 s y).mpr ⟨hsD, hiy⟩)
      exact ex ▸ ey ▸ ((code.2 x' y').mp hxy).2.2)
  obtain ⟨D₁, hD₁X, hD₁⟩ := source.space_l hZF hm
  let ρ : Env M 4 := ⟨Fin.cases g' (Fin.cases B₀ (Fin.cases κ (fun _ => n))), fun _ => n⟩
  let φ : UnarySchema 4 := { body := en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B₂, hB₂X, bs₂⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory
    φ (en_graph_delta_l ..) ρ (Fin.cases hg'X (Fin.cases hB₀X
      (Fin.cases source.cardinal_mem (fun _ => source.transitive ω source.omega_mem n hn)))) hD₁X
  have read s : M.mem s B₂ ↔ M.mem s D₁ ∧ En_graph_d n κ B₀ g' s :=
    (bs₂ s).trans (and_congr_right fun _ => en_graph_sat_l hZF.1 ..)
  have hB₂V := (family.at_l hZF.1 hbV hb hD₁).upward B₁ B₂ hB₁V hB₂X
    (fun s hs => ((read s).mp hs).1) (fun s hs => (read s).mpr
      ⟨(family.at_l hZF.1 hbV hb hD₁).base.bounds B₁ hB₁V s hs, graph s hs⟩)
  -- 新末坐标可能已经出现；统一覆盖到单射支撑后再作商计算。
  obtain ⟨l, d, r₁, _, hl, hd, hr₁, hrb, _⟩ := ec_join_l hZF source.omega hm hm hb hb
  have hd' := fn0_of_function_l (ZF.modelsKP hZF) hd.1
  have hdJ := (h.indices d).mpr ⟨l, hl, hd', hd.2⟩
  have sub i x (hix : Rd_entry_d i x c) : Rd_entry_d i x b := hix.elim fun p hp => ⟨p, hp.1, hcb p hp.2⟩
  obtain ⟨r₀, hr₀, hrc⟩ := ec_factor_l hZF hc hd (fun i x hix => by
    obtain ⟨j, _, hij⟩ := hr₁.2.1 i (hb.bound_l (sub i x hix)).1
    exact ⟨j, (hrb.value_l hr₁ hd' hij).mp (sub i x hix)⟩)
  have same i j k (hij : Rd_entry_d i j r₀) (hik : Rd_entry_d i k r₁) : j = k := by
    obtain ⟨x, _, hix⟩ := hc.2.1 i (hr₀.bound_l hij).1
    exact hd.2 j k x ((hrc.value_l hr₀ hd' hij).mp hix) ((hrb.value_l hr₁ hd' hik).mp (sub i x hix))
  obtain ⟨D₂, _, hD₂⟩ := source.space_l hZF hl
  obtain ⟨g₂, _, _, pull, repr₂⟩ := ep_repr_reindex_l hZF source family h limit hn hl hr₀ hdJ hd' hrc hD hD₂
    hg'X (hg'.mono_target_l (source.transitive κ source.cardinal_mem)) repr
  obtain ⟨j, hj, hnj⟩ := hr₁.2.1 n hmn.predecessor_mem
  obtain ⟨f₂, hf₂X, hf₂⟩ := source.coordinate_l hZF hl hD₂ hj
  obtain ⟨E₂, _, value₂⟩ := ep_repr_exists_l hZF family h limit hdJ hd' hD₂ hf₂X
    (hf₂.1.mono_target_l (source.transitive κ source.cardinal_mem))
  obtain ⟨U₂, hdU⟩ := family.total l d hl hd'
  obtain ⟨B₃, bs₃, measure⟩ := coherent m l r₁ d b V₀ U₂ B₂ hm hl hB₂X hr₁ hd' hrb hdU hbV
    (fun s hs => (hD₁ s).mp ((read s).mp hs).1)
  have equal : Rp_eq_d X U₂ g₂ f₂ := by
    refine ⟨B₃, measure.mpr hB₂V, fun s hs => ?_⟩
    obtain ⟨hs, t, ht, hst⟩ := (bs₃ s).mp hs
    obtain ⟨_, v, hv, hvt, x, hx, hvx, hnx⟩ := (read t).mp ht
    have hvD := ((bs₀ v).mp hv).1
    have hvFn := (hD v).mp hvD
    have comp : Cp0_d n l κ r₀ s v := by
      refine ⟨hvFn, fun i hi => ?_⟩
      obtain ⟨k, hk, hik⟩ := hr₀.2.1 i hi
      obtain ⟨k', _, hik'⟩ := hr₁.2.1 i ((hmn i).mpr (Or.inl hi))
      have ek := same i k k' hik hik'
      obtain ⟨y, hy, hiy⟩ := hvFn.2.1 i hi
      exact ⟨k, hk, y, hy, hik, (hst.value_l hr₁ hs (ek.symm ▸ hik')).mp
        (hiy.elim fun p hp => ⟨p, hp.1, hvt p hp.2⟩), hiy⟩
    exact ⟨x, source.transitive κ source.cardinal_mem x hx, (pull.2.2 s v hs comp x).mpr hvx,
      (hf₂.2 s x).mpr ⟨(hD₂ s).mpr hs, (hst.value_l hr₁ hs hnj).mp hnx⟩⟩
  have eH₂ := (ep_repr_atoms_l hZF family h limit hdU repr₂ value₂).1.mpr equal
  exact ⟨β, hβα, l, d, j, D₂, f₂, hd', (hrb.value_l hr₁ hd' hnj).mp hnβ, hD₂, hf₂, eH₂.symm ▸ value₂⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原始关系超幂中的完整支撑初段

坐标类给出 L 的单射像，正规性保证该像对原商中的全部前驱封闭。
倒转坐标图便得到这个初段的实际坍塌；整个商可以仍然不良基。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_seed_segment_l {ω κ K L X R F J O Z A p T S q C W : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L)
     (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W) :
    ∃ B r, M.MemberSubset B C ∧ Wc_map_d B W L r ∧ M.IsSetBijectionFromTo I r B L ∧
      (∀ E α, Rd_entry_d E α r ↔ Ep_seed_d κ L q α E) ∧
      ∀ E H, M.mem E B → Rd_entry_d H E W → M.mem H B := by
  have bound α E (seed : Ep_seed_d κ L q α E) : M.mem α L ∧ M.mem E C := by
    obtain ⟨_, a, i, _, _, ha, hi, _, _, u, B, _, _, hu⟩ := seed
    exact ⟨(ha.bound_l hi).2, (limit.projection.bound_l hu).2⟩
  let ρ : Env M 3 := ⟨Fin.cases κ (Fin.cases L (fun _ => q)), fun _ => L⟩
  let φ : BinarySchema 3 := { body := ep_seed_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest }
  have sat α E : φ.denote ρ α E ↔ Ep_seed_d κ L q α E := ep_seed_sat_l hZF.1 ..
  obtain ⟨i, fi, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := L) (target := C)
    (fun α hα => (ep_seed_exists_l hZF source family system limit hα).imp fun E h => (sat α E).mpr h.2)
    (fun α _ E H he hh => (ep_seed_atoms_l hZF source family atoms system limit
      ((sat α E).mp he) ((sat α H).mp hh)).1.mpr rfl)
    (fun α E _ he => (bound α E ((sat α E).mp he)).2)
  have read α E : Rd_entry_d α E i ↔ Ep_seed_d κ L q α E :=
    (spec α E).trans ((and_congr_right fun _ => sat α E).trans
      ⟨And.right, fun seed => ⟨(bound α E seed).1, seed⟩⟩)
  obtain ⟨B, range⟩ := ZF.exists_range_of_setFunction hZF I fi.1 fi.2.1
  have bij : M.IsSetBijectionFromTo I i L B := ⟨⟨⟨fi.1, fi.2.1, fun α hα =>
    (fi.2.2 α hα).imp fun E he => ⟨(range E).mpr ⟨α, he.2⟩, he.2⟩⟩,
    fun α β E hα hβ => (ep_seed_atoms_l hZF source family atoms system limit
      ((read α E).mp hα) ((read β E).mp hβ)).1.mp rfl⟩,
    fun E hE => ((range E).mp hE).imp fun α h => ⟨fi.input_mem_of_pairMember h, h⟩⟩
  obtain ⟨r, fr, inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have decode E α : Rd_entry_d E α r ↔ Ep_seed_d κ L q α E := (inverse E α).trans (read α E)
  have sub E (hE : M.mem E B) : M.mem E C := by
    obtain ⟨α, hα⟩ := (range E).mp hE
    exact fi.output_mem_of_pairMember hα
  have down E H (hE : M.mem E B) (edge : Rd_entry_d H E W) : M.mem H B := by
    obtain ⟨α, hα⟩ := (range E).mp hE
    obtain ⟨β, _, seed⟩ := ep_seed_down_l hZF source hκ family coherent normal system limit ((read α E).mp hα) edge
    exact (range H).mpr ⟨β, (read β H).mpr seed⟩
  refine ⟨B, r, sub, ⟨hL, fn0_of_function_l (ZF.modelsKP hZF) fr.1.1,
    fun α hα => (fr.2 α hα).imp fun _ h => h, ?_⟩, fr, decode, down⟩
  intro E hE α hα hEα β hβ
  constructor
  · intro hβα
    obtain ⟨H, _, hHβ⟩ := fr.2 β hβ
    exact ⟨H, fr.1.1.input_mem_of_pairMember hHβ,
      (ep_seed_atoms_l hZF source family atoms system limit ((decode H β).mp hHβ) ((decode E α).mp hEα)).2.mpr hβα, hHβ⟩
  · rintro ⟨H, _, edge, hHβ⟩
    exact (ep_seed_atoms_l hZF source family atoms system limit ((decode H β).mp hHβ) ((decode E α).mp hEα)).2.mp edge

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 坍塌把坐标类精确识别为支撑序数

支撑初段已经独立于整体坍塌构造。把给定坍塌限制到该初段，局部递归
唯一性就识别出原支撑序数；不再重复坐标初段的构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_seed_collapse_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q C W N e : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L)
     (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (collapse : Wc_graph_d C W e) (he : Fn0_d C N e) :
    M.MemberSubset L N ∧ ∀ α E, Ep_seed_d κ L q α E → Rd_entry_d E α e := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, r, sub, map, _, read, down⟩ := ep_seed_segment_l hZF source hκ hL family coherent atoms normal h limit
  obtain ⟨s, restriction⟩ := ZF.exists_restriction hZF I e B
  have fs := restriction.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) he) sub
  have graph : Wc_graph_d B W s := by
    refine ⟨fs.1.1, fun E α entry => ?_⟩
    obtain ⟨hE, original⟩ := (restriction.2 E α).mp entry
    refine ⟨hE, ?_, fun β => ?_⟩
    · intro H hH edge
      obtain ⟨β, _, hHβ⟩ := he.2.1 H (sub H hH)
      exact ⟨β, (restriction.2 H β).mpr ⟨hH, hHβ⟩⟩
    · rw [(collapse.2 E α original).2.2 β]
      exact ⟨fun ⟨H, _, edge, hHβ⟩ => ⟨H, down E H hE edge, edge,
        (restriction.2 H β).mpr ⟨down E H hE edge, hHβ⟩⟩,
        fun ⟨H, hH, edge, hHβ⟩ => ⟨H, sub H hH, edge, ((restriction.2 H β).mp hHβ).2⟩⟩
  have fixed : ∀ α E, Ep_seed_d κ L q α E → Rd_entry_d E α e := by
    intro α E seed
    have hEα := (read E α).mpr seed
    obtain ⟨β, _, hEβ⟩ := fs.2.2 E (map.function.bound_l hEα).1
    have eq := wc_value_unique_l hZF (map.well_founded_l (ZF.modelsKP hZF))
      ⟨s, graph, hEβ⟩ ⟨r, map.graph_l, hEα⟩
    exact eq ▸ ((restriction.2 E β).mp hEβ).2
  exact ⟨fun α hα => by
    obtain ⟨E, _, hs⟩ := ep_seed_exists_l hZF source family h limit hα
    exact (he.bound_l (fixed α E hs)).2, fixed⟩

end YesMetaZFC.SetTheory.LargeCardinal
