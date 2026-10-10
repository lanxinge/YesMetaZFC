import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCoordinateSource

/-! # 扩展器支撑在同一商极限中的坐标像

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

theorem ep_seed_exists_l (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
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
theorem ep_seed_move_l (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
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

theorem ep_seed_atoms_l (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
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
