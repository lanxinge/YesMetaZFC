import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakHistory
import YesMetaZFC.SetTheory.LargeCardinal.IterationLinearOrder
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # 任意极限长度的相容弱迭代历史取并

模型、箭头和返回三列逐项取并；函数性在两个旧行的共同后继验证。
含给定指标的旧行给出并图的精确限制，所有有限元条件因而回到原状态。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
private def wi_pick {A : Type u} (Q G P : A) : Fin 3 → A := Fin.cases Q (Fin.cases G (fun _ => P))
private def Wi_union_d (k : Fin 3) (H x : M.Domain) : Prop := ∃ i s T Q G P,
  Rd_entry_d i s H ∧ Rd_quad_d s T Q G P ∧ M.mem x (wi_pick Q G P k)
private def wi_union_m (k : Fin 3) {d} (H x : Term d) : Formula 1 d := set[d] ⟪
  ∃ i s T Q G P, ⌜rd_entry0_m⌝ₚ(i, s, ⌜H⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(s, T, Q, G, P) ∧
    ⌜(fun Q G P x => (Definitional.Formula.mem x (wi_pick Q G P k) : Formula 1 _))⌝ₚ(Q, G, P, ⌜x⌝ₛ)⟫
@[simp] private theorem wi_union_closed_l (k : Fin 3) {d} (H x : Term d)
    (hH : H.freeSupport = []) (hx : x.freeSupport = []) : (wi_union_m k H x).FreeClosed := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) k <;>
    simp -implicitDefEqProofs [wi_union_m, wi_pick, Definitional.Formula.FreeClosed, hH, hx] <;> rfl
private theorem wi_union_sat_l (hE : Extensional M) (k : Fin 3) {d} (η : Env M d) (H x : Term d) :
    Formula.satisfies η (wi_union_m k H x) ↔ Wi_union_d k (H.eval η) (x.eval η) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) k <;>
    simp only [wi_union_m, Wi_union_d, wi_pick, Fin.cases_zero, Fin.cases_succ,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      rd_entry0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken] <;> rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_history_d.union_l {ω a A S α D H : M.Domain} (hist : Wi_history_d hZF ω a A S α D H)
    (limit : M.IsLimitOrdinal α) : ∃ T Q G P, Wi_state_d hZF ω α T Q G a A S P ∧
      ∀ i U Q' G' P', Wi_at_d H i U Q' G' P' → Wi_keep_d Q' G' P' Q G P := by
  have ff := fn0_function_l (ZF.modelsKP hZF) hist.function
  have read {i s T Q G P} (hs : Rd_entry_d i s H) (pack : Rd_quad_d s T Q G P) := hist.at_l hZF ⟨s, hs, pack⟩
  have self {Q G P : M.Domain} : Wi_keep_d (M := M) Q G P Q G P := Wi_keep_d.refl_l Q G P
  have merge {i j s t T Q G P U Q' G' P'} (hs : Rd_entry_d i s H) (ht : Rd_entry_d j t H)
      (ps : Rd_quad_d s T Q G P) (pt : Rd_quad_d t U Q' G' P') :
      ∃ k v V Q'' G'' P'', Rd_entry_d k v H ∧ Rd_quad_d v V Q'' G'' P'' ∧
        Wi_keep_d Q G P Q'' G'' P'' ∧ Wi_keep_d Q' G' P' Q'' G'' P'' := by
    rcases limit.1.wellOrder.linear.compare i (hist.function.bound_l hs).1 j (hist.function.bound_l ht).1 with eq | lt | gt
    · have eq := hZF.1.eq_of_same_members i j eq
      subst j
      have eq := ff.1.2 i t s ht hs
      subst t
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ps.unique_l pt
      exact ⟨i, s, T, Q, G, P, hs, ps, self, self⟩
    · exact ⟨j, t, U, Q', G', P', ht, pt, hist.past i j T Q G P U Q' G' P' lt ⟨s, hs, ps⟩ ⟨t, ht, pt⟩, self⟩
    · exact ⟨i, s, T, Q, G, P, hs, ps, self, hist.past j i U Q' G' P' T Q G P gt ⟨t, ht, pt⟩ ⟨s, hs, ps⟩⟩
  have part {β T Q G P} (state : Wi_state_d hZF ω β T Q G a A S P) (k : Fin 3) : M.IsSetFunction I (wi_pick Q G P k) :=
    Fin.cases state.diagram.model_function (Fin.cases state.diagram.map_function (fun _ => state.returns.function)) k
  have keeps {β T Q G P Q' G' P'} (state : Wi_state_d hZF ω β T Q G a A S P)
      (keep : Wi_keep_d Q G P Q' G' P') (k : Fin 3) :
      ∀ x y, Rd_entry_d x y (wi_pick Q G P k) → Rd_entry_d x y (wi_pick Q' G' P' k) := by
    refine Fin.cases keep.1 (Fin.cases ?_ (fun _ => keep.2.2)) k
    intro r f hr
    obtain ⟨i, j, pair⟩ := state.diagram.order.relation r ((state.diagram.map_domain r).mpr ⟨f, hr⟩)
    obtain ⟨r', pair', hr'⟩ := keep.2.1 i j f ⟨r, pair, hr⟩
    exact kpair_unique_l M hZF.1 pair' pair ▸ hr'
  obtain ⟨Z, zt, hD, _⟩ := ZF.tc_exists_l I hZF D
  have collect (k : Fin 3) : ∃ C, ∀ x, M.mem x C ↔ Wi_union_d k H x := by
    let φ : UnarySchema 1 := { body := wi_union_m k (.bound 1) .newest }
    let ρ : Env M 1 := ⟨fun _ => H, fun _ => H⟩
    obtain ⟨C, cs⟩ := ZF.separation_exists_d hZF φ ρ Z
    refine ⟨C, fun x => (cs x).trans ?_⟩
    change (M.mem x Z ∧ φ.denote ρ x) ↔ _
    rw [show φ.denote ρ x ↔ Wi_union_d k H x from wi_union_sat_l hZF.1 k ..]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    obtain ⟨i, s, T, Q, G, P, hs, pack, hx⟩ := h
    have owned := pack.mem_l zt (zt D hD s (hist.function.bound_l hs).2)
    have hk : M.mem (wi_pick Q G P k) Z := by
      refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) k
      · exact owned.2.1
      · exact owned.2.2.1
      · exact owned.2.2.2
    exact zt _ hk x hx
  have graphs (k : Fin 3) {C} (cs : ∀ x, M.mem x C ↔ Wi_union_d k H x) : M.IsSetFunction I C ∧
      ∀ x y, Rd_entry_d x y C ↔ ∃ i s T Q G P, Rd_entry_d i s H ∧ Rd_quad_d s T Q G P ∧ Rd_entry_d x y (wi_pick Q G P k) := by
    have entries x y : Rd_entry_d x y C ↔ ∃ i s T Q G P, Rd_entry_d i s H ∧ Rd_quad_d s T Q G P ∧ Rd_entry_d x y (wi_pick Q G P k) := by
      refine ⟨fun ⟨r, pair, hr⟩ => ?_, fun ⟨i, s, T, Q, G, P, hs, pack, r, pair, hr⟩ => ?_⟩
      · obtain ⟨i, s, T, Q, G, P, hs, pack, hr⟩ := (cs r).mp hr
        exact ⟨i, s, T, Q, G, P, hs, pack, r, pair, hr⟩
      · exact ⟨r, pair, (cs r).mpr ⟨i, s, T, Q, G, P, hs, pack, hr⟩⟩
    refine ⟨⟨fun r hr => ?_, fun x y z hy hz => ?_⟩, entries⟩
    · obtain ⟨i, s, T, Q, G, P, hs, pack, hr⟩ := (cs r).mp hr
      obtain ⟨_, _, state⟩ := read hs pack
      exact (part state k).1 r hr
    · obtain ⟨i, s, T, Q, G, P, hs, pack, hy⟩ := (entries x y).mp hy
      obtain ⟨j, t, U, Q', G', P', ht, pack', hz⟩ := (entries x z).mp hz
      obtain ⟨l, v, V, Q'', G'', P'', hv, pv, sv, tv⟩ := merge hs ht pack pack'
      obtain ⟨_, _, st⟩ := read hv pv
      obtain ⟨_, _, si⟩ := read hs pack
      obtain ⟨_, _, sj⟩ := read ht pack'
      exact (part st k).2 x y z (keeps si sv k x y hy) (keeps sj tv k x z hz)
  obtain ⟨Q, qs⟩ := collect 0
  obtain ⟨G, gs⟩ := collect 1
  obtain ⟨P, ps⟩ := collect 2
  obtain ⟨qf, qe⟩ := graphs 0 qs
  obtain ⟨gf, ge⟩ := graphs 1 gs
  obtain ⟨pf, pe⟩ := graphs 2 ps
  have edge i j f : It_map_d G i j f ↔ ∃ k s T Q G' P,
      Rd_entry_d k s H ∧ Rd_quad_d s T Q G' P ∧ It_map_d G' i j f := by
    refine ⟨fun ⟨r, pair, hr⟩ => ?_, fun ⟨k, s, T, Q, G', P, hs, pack, r, pair, hr⟩ => ?_⟩
    · obtain ⟨k, s, T, Q, G', P, hs, pack, hr⟩ := (ge r f).mp hr
      exact ⟨k, s, T, Q, G', P, hs, pack, r, pair, hr⟩
    · exact ⟨r, pair, (ge r f).mpr ⟨k, s, T, Q, G', P, hs, pack, hr⟩⟩
  have keep {i U Q' G' P'} (hi : Wi_at_d H i U Q' G' P') : Wi_keep_d Q' G' P' Q G P := by
    obtain ⟨s, hs, pack⟩ := hi
    exact ⟨fun j c hc => (qe j c).mpr ⟨i, s, U, Q', G', P', hs, pack, hc⟩,
      fun j k f hf => (edge j k f).mpr ⟨i, s, U, Q', G', P', hs, pack, hf⟩,
      fun j f hf => (pe j f).mpr ⟨i, s, U, Q', G', P', hs, pack, hf⟩⟩
  have stage i (hi : M.mem i α) : ∃ β U Q' G' P', M.SuccessorOf β i ∧ Wi_at_d H i U Q' G' P' ∧ Wi_state_d hZF ω β U Q' G' a A S P' := by
    obtain ⟨s, _, hs⟩ := hist.function.2.1 i hi
    obtain ⟨β, U, Q', G', P', hβ, pack, state⟩ := hist.rows i s hs
    exact ⟨β, U, Q', G', P', hβ, ⟨s, hs, pack⟩, state⟩
  have below {i β j} (hi : M.mem i α) (hβ : M.SuccessorOf β i) (hj : M.mem j β) : M.mem j α :=
    ((hβ j).mp hj).elim (limit.1.transitive i hi j) (fun eq => (hZF.1.eq_of_same_members j i eq).symm ▸ hi)
  have qold {i β U Q' G' P'} (hi : Wi_at_d H i U Q' G' P') (st : Wi_state_d hZF ω β U Q' G' a A S P')
      {j c} (hj : M.mem j β) : Rd_entry_d j c Q ↔ Rd_entry_d j c Q' := by
    refine ⟨fun hc => ?_, (keep hi).1 j c⟩
    obtain ⟨d, hd⟩ := (st.diagram.model_domain j).mp hj
    exact qf.2 j d c ((keep hi).1 j d hd) hc ▸ hd
  have pold {i β U Q' G' P'} (hi : Wi_at_d H i U Q' G' P') (st : Wi_state_d hZF ω β U Q' G' a A S P')
      {j f} (hj : M.mem j β) : Rd_entry_d j f P ↔ Rd_entry_d j f P' := by
    refine ⟨fun hf => ?_, (keep hi).2.2 j f⟩
    obtain ⟨g, hg⟩ := (st.returns.domain j).mp hj
    exact pf.2 j g f ((keep hi).2.2 j g hg) hf ▸ hg
  have bounds {i j f} (hf : It_map_d G i j f) : M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j) := by
    obtain ⟨k, s, U, Q', G', P', hs, pack, hf⟩ := (edge i j f).mp hf
    obtain ⟨β, hβ, st⟩ := read hs pack
    have h := st.diagram.map_bound_l hZF hf
    exact ⟨below (hist.function.bound_l hs).1 hβ (st.diagram.order.bound i j h).1,
      below (hist.function.bound_l hs).1 hβ (st.diagram.order.bound i j h).2, st.diagram.order.forward i j h⟩
  have gold {k β U Q' G' P'} (hk : Wi_at_d H k U Q' G' P') (st : Wi_state_d hZF ω β U Q' G' a A S P')
      {i j f} (hj : M.mem j β) (hf : It_map_d G i j f) : It_map_d G' i j f := by
    have ij := (bounds hf).2.2
    have hit : Rd_entry_d i j U := ij.elim (fun eq => eq.symm ▸ st.diagram.order.refl j hj) (st.linear i j hj)
    obtain ⟨g, hg⟩ := st.diagram.map_l hZF hit
    obtain ⟨r, pr, hr⟩ := (keep hk).2.1 i j g hg
    obtain ⟨s, ps, hs⟩ := hf
    exact gf.2 r g f hr (kpair_unique_l M hZF.1 ps pr ▸ hs) ▸ hg
  obtain ⟨T, order, ts, _⟩ := it_linear_order_l (ZF.modelsKP hZF) limit.1
  have qdom : M.IsDomainOf I α Q := by
    intro i
    refine ⟨fun hi => ?_, fun ⟨c, hc⟩ => ?_⟩
    · obtain ⟨β, U, Q', G', P', hβ, hi', st⟩ := stage i hi
      obtain ⟨c, hc⟩ := (st.diagram.model_domain i).mp hβ.predecessor_mem
      exact ⟨c, (keep hi').1 i c hc⟩
    · obtain ⟨k, s, U, Q', G', P', hs, pack, hc⟩ := (qe i c).mp hc
      obtain ⟨β, hβ, st⟩ := read hs pack
      exact below (hist.function.bound_l hs).1 hβ ((st.diagram.model_domain i).mpr ⟨c, hc⟩)
  have pdom : M.IsDomainOf I α P := by
    intro i
    refine ⟨fun hi => ?_, fun ⟨f, hf⟩ => ?_⟩
    · obtain ⟨β, U, Q', G', P', hβ, hi', st⟩ := stage i hi
      obtain ⟨f, hf⟩ := (st.returns.domain i).mp hβ.predecessor_mem
      exact ⟨f, (keep hi').2.2 i f hf⟩
    · obtain ⟨k, s, U, Q', G', P', hs, pack, hf⟩ := (pe i f).mp hf
      obtain ⟨β, hβ, st⟩ := read hs pack
      exact below (hist.function.bound_l hs).1 hβ ((st.returns.domain i).mpr ⟨f, hf⟩)
  have gdom : M.IsDomainOf I T G := by
    intro r
    refine ⟨fun hr => ?_, fun ⟨f, hr⟩ => ?_⟩
    · obtain ⟨i, j, pair⟩ := order.relation r hr
      obtain ⟨_, hj, ij⟩ := (ts i j).mp ⟨r, pair, hr⟩
      obtain ⟨β, U, Q', G', P', hβ, hj', st⟩ := stage j hj
      have hit : Rd_entry_d i j U := ij.elim (fun eq => eq.symm ▸ st.diagram.order.refl j hβ.predecessor_mem) (st.linear i j hβ.predecessor_mem)
      obtain ⟨f, hf⟩ := st.diagram.map_l hZF hit
      obtain ⟨r', pair', hr'⟩ := (keep hj').2.1 i j f hf
      exact ⟨f, kpair_unique_l M hZF.1 pair' pair ▸ hr'⟩
    · obtain ⟨k, s, U, Q', G', P', hs, pack, hr'⟩ := (ge r f).mp hr
      obtain ⟨_, _, st⟩ := read hs pack
      obtain ⟨i, j, pair⟩ := st.diagram.order.relation r ((st.diagram.map_domain r).mpr ⟨f, hr'⟩)
      obtain ⟨r', pair', hrT⟩ := (ts i j).mpr (bounds ⟨r, pair, hr⟩)
      exact kpair_unique_l M hZF.1 pair' pair ▸ hrT
  have sources i c (hc : Rd_entry_d i c Q) : It_source_d hZF ω c := by
    obtain ⟨k, s, U, Q', G', P', hs, pack, hc⟩ := (qe i c).mp hc
    obtain ⟨_, _, st⟩ := read hs pack
    exact st.sources i c hc
  have diagram : It_diagram_d hZF ω α T Q G := by
    refine ⟨order, qf, qdom, fun i c hc => ?_, gf, gdom, ?_, ?_, ?_⟩
    · obtain ⟨X, R, _, mx, _⟩ := sources i c hc
      exact ⟨X, R, mx.1⟩
    · intro i j f c X R d Y W hf hc hd mx my
      obtain ⟨β, U, Q', G', P', hβ, hj', st⟩ := stage j (bounds hf).2.1
      have edge := gold hj' st hβ.predecessor_mem hf
      have hi := (st.diagram.order.bound i j (st.diagram.map_bound_l hZF edge)).1
      exact st.diagram.elementary i j f c X R d Y W edge ((qold hj' st hi).mp hc) ((qold hj' st hβ.predecessor_mem).mp hd) mx my
    · intro i f hf x y hxy
      obtain ⟨k, s, U, Q', G', P', hs, pack, hf⟩ := (edge i i f).mp hf
      obtain ⟨_, _, st⟩ := read hs pack
      exact st.diagram.identity i f hf x y hxy
    · intro i j k f g h hf hg hh x y z hxy hyz
      obtain ⟨β, U, Q', G', P', hβ, hk', st⟩ := stage k (bounds hg).2.1
      have g' := gold hk' st hβ.predecessor_mem hg
      have hj := (st.diagram.order.bound j k (st.diagram.map_bound_l hZF g')).1
      exact st.diagram.comp i j k f g h (gold hk' st hj hf) g' (gold hk' st hβ.predecessor_mem hh) x y z hxy hyz
  obtain ⟨o, ho⟩ := limit.2.1
  obtain ⟨_, _, _, _, _, _, _, first⟩ := stage o ho
  refine ⟨T, Q, G, P, ⟨diagram, fun i j hj hij => (ts i j).mpr ⟨limit.1.transitive j hj i hij, hj, Or.inr hij⟩,
    sources, ?_, ⟨first.returns.model, pf, pdom, ?_, ?_⟩⟩, fun _ _ _ _ _ hi => keep hi⟩
  · intro i c X R hc pair
    obtain ⟨k, s, U, Q', G', P', hs, pack, hc⟩ := (qe i c).mp hc
    obtain ⟨_, _, st⟩ := read hs pack
    exact st.count i c X R hc pair
  · intro i f c X R hf hc mx
    obtain ⟨β, U, Q', G', P', hβ, hi', st⟩ := stage i ((pdom i).mpr ⟨f, hf⟩)
    exact st.returns.elementary i f c X R ((pold hi' st hβ.predecessor_mem).mp hf) ((qold hi' st hβ.predecessor_mem).mp hc) mx
  · intro i j f u v hf hu hv x y z hxy hyz
    obtain ⟨β, U, Q', G', P', hβ, hj', st⟩ := stage j (bounds hf).2.1
    have edge := gold hj' st hβ.predecessor_mem hf
    have hi := (st.diagram.order.bound i j (st.diagram.map_bound_l hZF edge)).1
    exact st.returns.commute i j f u v edge ((pold hj' st hi).mp hu) ((pold hj' st hβ.predecessor_mem).mp hv) x y z hxy hyz

end YesMetaZFC.SetTheory.LargeCardinal
