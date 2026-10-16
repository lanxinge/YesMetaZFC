import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunOrder
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # 统一有限树列的内部并

先从记录值域的传递闭包分离各列。任意有限组条目回到共同阶段核验；
旧终点的全部前驱保持使并树在每个旧阶段上的限制精确等于原树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_run_value_d (a : Fin 64) (f x : M.Domain) : Prop := ∃ q : Fin 64 → M.Domain,
  ∃ i s, Rd_entry_d i s f ∧ Rt_tuple_d q s ∧ M.mem x (q a)

private def tg_run_value_body_m (a : Fin 64) : Formula 1 66 := .existsE (.existsE
  (.conj (rd_entry0_m (.bound 1) .newest (.bound 66))
    (.conj (rt_tuple_m (fun i : Fin 64 => .bound (i.castAdd 2).succ.succ) .newest)
      (.mem (.bound 67) (.bound (a.castAdd 2).succ.succ)))))
def tg_run_value0_m (a : Fin 64) : Formula 1 2 := rt_exists_m 64 (tg_run_value_body_m a)

theorem tg_run_value0_closed_l (a : Fin 64) : (tg_run_value0_m a).FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  simp -implicitDefEqProofs [tg_run_value_body_m, Definitional.Formula.FreeClosed]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_run_value0_sat_l (hE : Extensional M) (a : Fin 64) (η : Env M 2) :
    Formula.satisfies η (tg_run_value0_m a) ↔ Tg_run_value_d a (η.bound 0) (η.bound 1) := by
  rw [tg_run_value0_m, rt_exists_sat_l]
  apply exists_congr
  intro q
  have new (i : Fin 64) : (rt_push_d η 64 q).bound (i.castAdd 2) = q i := rt_push_new_l η q i
  simp only [tg_run_value_body_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, rt_tuple_sat_l hE, Formula.satisfies_mem_iff,
    Term.eval_bound]
  change (∃ i s, Rd_entry_d i s ((rt_push_d η 64 q).bound 64) ∧
    Rt_tuple_d (fun j => (rt_push_d η 64 q).bound (j.castAdd 2)) s ∧
    M.mem ((rt_push_d η 64 q).bound 65) ((rt_push_d η 64 q).bound (a.castAdd 2))) ↔ _
  simp only [new]
  rw [show (rt_push_d η 64 q).bound 64 = η.bound 0 from rt_push_old_l η q 0,
    show (rt_push_d η 64 q).bound 65 = η.bound 1 from rt_push_old_l η q 1]

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_sequence_d (ω c o C γ Z A D f : M.Domain) : Prop where
  function : Fn0_d ω D f
  rows : ∀ i s, Rd_entry_d i s f → ∃ n, M.SuccessorOf n i ∧ Tg_run_code_d hZF ω c o C γ Z A n s
  steps : ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s f → Rd_entry_d j t f → Tg_run_edge_d hZF ω c s t

theorem Tg_sequence_d.read_l {ω c o C γ Z A D f : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) {i s} {v : Fin 64 → M.Domain}
    (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) :
    Tg_run_d hZF ω c o C γ Z A (fun j => v (j.castAdd 46)) (fun j => v (Fin.natAdd 18 j)) ∧ M.mem i (v 6) := by
  obtain ⟨n, ns, q, pack, run, num⟩ := h.rows i s hs
  have eq := rt_tuple_inj_l pack code
  subst q
  exact ⟨run, run.tree.tree.diagram.order.ordinal.transitive n (num ▸ run.span) i ns.predecessor_mem⟩

/-- 并列中的每个真实扩展器来自某一有限轮，故保留同一个临界点下界。 -/
theorem Tg_sequence_d.critical_bound_l {ω c o C γ Z A D f E : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (column : ∀ x, M.mem x E ↔ Tg_run_value_d 11 f x) : It_critical_bound_d γ E := by
  rintro i p κ L F ⟨q, pair, hq⟩ payload
  obtain ⟨v, n, s, hs, code, hq⟩ := (column q).mp hq
  exact (h.read_l hZF hs code).1.critical i p κ L F ⟨q, pair, hq⟩ payload

theorem Tg_sequence_d.merge_l {ω c o C γ Z A D f : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hω : M.IsOmega ω) {i j s t} {v w : Fin 64 → M.Domain}
    (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    ∃ k r, ∃ z : Fin 64 → M.Domain, Rd_entry_d k r f ∧ Rt_tuple_d z r ∧ Tg_tree_keep_d v z ∧ Tg_tree_keep_d w z := by
  have read {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) := h.read_l hZF hs code
  have next {i j s t} (ij : M.SuccessorOf j i) (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) : Tg_run_keep_d s t := by
    obtain ⟨q, ps, pt, step⟩ := h.steps i j s t ij hs ht
    exact ⟨_, _, ps, pt, step.keep_l hZF (read hs ps).1 (read ht pt).1⟩
  let η : Env M 0 := ⟨Fin.elim0, fun _ => f⟩
  let φ : BinarySchema 0 := { body := tg_run_keep_m (.bound 1) .newest }
  have sat s t : φ.denote η s t ↔ Tg_run_keep_d s t := tg_run_keep_sat_l hZF.1 ..
  have chain := ZF.rel_chain_l I hZF φ η hω (fn0_function_l (ZF.modelsKP hZF) h.function)
    (fun _ _ _ _ _ _ a b => (sat _ _).mpr (((sat _ _).mp a).trans_l ((sat _ _).mp b)))
    (fun _ _ _ _ ij hs ht => (sat _ _).mpr (next ij hs ht))
  have mono {i j s t} {v w : Fin 64 → M.Domain} (ij : M.mem i j)
      (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) : Tg_tree_keep_d v w := by
    obtain ⟨v', w', ps', pt', keep⟩ := (sat _ _).mp (chain i j s t ij hs ht)
    have ev := rt_tuple_inj_l ps' ps
    have ew := rt_tuple_inj_l pt' pt
    exact ev ▸ ew ▸ keep
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare i (h.function.bound_l hs).1 j (h.function.bound_l ht).1 with eq | ij | ji
  · have eq := hZF.1.eq_of_same_members i j eq
    subst j
    have eq := (fn0_function_l (ZF.modelsKP hZF) h.function).1.2 i t s ht hs
    subst t
    have eq := rt_tuple_inj_l pt ps
    subst w
    exact ⟨i, s, v, hs, ps, .refl_l v, .refl_l v⟩
  · exact ⟨j, t, w, ht, pt, mono ij hs ht ps pt, .refl_l w⟩
  · exact ⟨i, s, v, hs, ps, .refl_l v, mono ji ht hs pt ps⟩

/-- 并树不增加任何旧终点的前驱；这里保留可直接用于奇数边的限制等式。 -/
theorem Tg_sequence_d.order_l {ω c o C γ Z A D f i s x y : M.Domain} {U : Fin 6 → M.Domain}
    {v : Fin 64 → M.Domain} (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω)
    (columns : ∀ a z, M.mem z (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f z)
    (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (hy : M.mem y (v 6)) :
    Rd_entry_d x y (U 0) ↔ Rd_entry_d x y (v 8) := by
  constructor
  · rintro ⟨p, pair, hp⟩
    obtain ⟨w, j, t, ht, pt, hp⟩ := (columns 0 p).mp hp
    obtain ⟨_, _, _, _, _, keep, keep'⟩ := h.merge_l hZF hw hs ht code pt
    exact (keep.2.1 x y hy).mp ⟨p, pair, keep'.2.2.1 0 p hp⟩
  · rintro ⟨p, pair, hp⟩
    exact ⟨p, pair, (columns 0 p).mpr ⟨v, i, s, hs, code, hp⟩⟩

theorem Tg_sequence_d.union_l {ω c o C γ Z A D f : M.Domain} (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (hω : M.IsOmega ω) : ∃ U : Fin 6 → M.Domain,
    It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4) ∧ M.IsSetFunction I (U 5) ∧
    ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x := by
  have read {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) := h.read_l hZF hs code
  have finite {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) : M.mem (v 6) ω := by
    have run := (read hs code).1
    obtain ⟨m, sm, hm⟩ := hω.1.2 (v 7) run.finite
    exact sm.eq hZF.1 run.successor ▸ hm
  have merge {i j s t} {v w : Fin 64 → M.Domain}
      (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) := h.merge_l hZF hω hs ht ps pt
  obtain ⟨B, bt, hDB, _⟩ := ZF.tc_exists_l I hZF D
  have collect (a : Fin 6) : ∃ U, ∀ x, M.mem x U ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x := by
    let ψ : UnarySchema 1 := {
      body := (tg_run_value0_m ⟨8+a.val, by omega⟩).bind (Fin.cases (.bound 1) (fun _ => .newest))
      freeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases rfl (fun _ => rfl)) _).mpr (tg_run_value0_closed_l _) }
    let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
    have value x : ψ.denote ρ x ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x := by
      rw [UnarySchema.denote, Formula.satisfies_bind, tg_run_value0_sat_l hZF.1]; rfl
    obtain ⟨U, us⟩ := ZF.separation_exists_d hZF ψ ρ B
    refine ⟨U, fun x => (us x).trans ((and_congr_right fun _ => value x).trans ⟨And.right, fun hx => ⟨?_, hx⟩⟩)⟩
    obtain ⟨q, i, s, hs, code, hx⟩ := hx
    exact bt _ (Rt_tuple_d.members_l (v := q) code bt (bt D hDB s (h.function.bound_l hs).2) _) x hx
  obtain ⟨T, ts⟩ := collect 0
  obtain ⟨Q, qs⟩ := collect 1
  obtain ⟨G, gs⟩ := collect 2
  obtain ⟨E, es⟩ := collect 3
  obtain ⟨L, ls⟩ := collect 4
  obtain ⟨H, hs⟩ := collect 5
  let U : Fin 6 → M.Domain := Fin.cases T (Fin.cases Q (Fin.cases G (Fin.cases E (Fin.cases L (fun _ => H)))))
  have us (a : Fin 6) (x) : M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x :=
    Fin.cases (ts x) (Fin.cases (qs x) (Fin.cases (gs x) (Fin.cases (es x)
      (Fin.cases (ls x) (Fin.cases (hs x) (fun i => Fin.elim0 i)))))) a
  have entries (a : Fin 6) (x y) : Rd_entry_d x y (U a) ↔ ∃ i s, ∃ v : Fin 64 → M.Domain,
      Rd_entry_d i s f ∧ Rt_tuple_d v s ∧ Rd_entry_d x y (v ⟨8+a.val, by omega⟩) := by
    refine ⟨fun ⟨p, pair, hp⟩ => ?_, fun ⟨i, s, v, hs, code, p, pair, hp⟩ => ?_⟩
    · obtain ⟨v, i, s, hs, code, hp⟩ := (us a p).mp hp
      exact ⟨i, s, v, hs, code, p, pair, hp⟩
    · exact ⟨p, pair, (us a p).mpr ⟨v, i, s, hs, code, hp⟩⟩
  have part {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (a : Fin 5) :
      M.IsSetFunction I (v ⟨8+a.succ.val, by omega⟩) := by
    have run := (read hs code).1
    exact Fin.cases run.tree.tree.diagram.model_function (Fin.cases run.tree.tree.diagram.map_function
      (Fin.cases run.tree.tree.move_function (Fin.cases run.tree.function
        (Fin.cases run.past.sequence.2.1 (fun i => Fin.elim0 i))))) a
  have functions (a : Fin 5) : M.IsSetFunction I (U a.succ) := by
    refine ⟨fun p hp => ?_, fun x y z hy hz => ?_⟩
    · obtain ⟨v, i, s, hs, code, hp⟩ := (us a.succ p).mp hp
      exact (part hs code a).1 p hp
    · obtain ⟨i, s, v, hs, ps, p, pair, hp⟩ := (entries a.succ x y).mp hy
      obtain ⟨j, t, w, ht, pt, q, qp, hq⟩ := (entries a.succ x z).mp hz
      obtain ⟨k, r, u, hr, pr, su, tu⟩ := merge hs ht ps pt
      exact (part hr pr a).2 x y z ⟨p, pair, su.2.2.1 a.succ p hp⟩ ⟨q, qp, tu.2.2.1 a.succ q hq⟩
  have inside {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (a : Fin 6) :
      M.MemberSubset (v ⟨8+a.val, by omega⟩) (U a) := fun x hx => (us a x).mpr ⟨v, i, s, hs, code, hx⟩
  have keeps {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (a : Fin 6)
      {x y} (xy : Rd_entry_d x y (v ⟨8+a.val, by omega⟩)) : Rd_entry_d x y (U a) :=
    (entries a x y).mpr ⟨i, s, v, hs, code, xy⟩
  have orderOld {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      {x y} (hy : M.mem y (v 6)) : Rd_entry_d x y (U 0) ↔ Rd_entry_d x y (v 8) :=
    h.order_l hZF hω us hs code hy
  have bound {i j} (ij : Rd_entry_d i j (U 0)) : M.mem i ω ∧ M.mem j ω := by
    obtain ⟨k, s, v, hs, code, ij⟩ := (entries 0 i j).mp ij
    have bounds := (read hs code).1.tree.tree.diagram.order.bound i j ij
    exact ⟨hω.transitive hZF _ (finite hs code) i bounds.1, hω.transitive hZF _ (finite hs code) j bounds.2⟩
  have stage (i) (hi : M.mem i ω) : ∃ s, ∃ v : Fin 64 → M.Domain, Rd_entry_d i s f ∧ Rt_tuple_d v s := by
    obtain ⟨s, _, hs⟩ := h.function.2.1 i hi
    obtain ⟨_, _, v, code, _⟩ := h.rows i s hs
    exact ⟨s, v, hs, code⟩
  -- 以下只在包含终点的旧阶段核验序、模型、箭头与扩展器。
  have order : It_order_d ω (U 0) := by
    refine ⟨hω.isOrdinal hZF, ?_, fun _ _ ij => bound ij, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨v, i, s, hs, code, hp⟩ := (us 0 p).mp hp
      exact (read hs code).1.tree.tree.diagram.order.relation p hp
    · intro i hi
      obtain ⟨s, v, hs, code⟩ := stage i hi
      exact keeps hs code 0 ((read hs code).1.tree.tree.diagram.order.refl i (read hs code).2)
    · intro i j k ij jk
      obtain ⟨s, v, hs, code⟩ := stage k (bound jk).2
      have st := (read hs code).1.tree.tree.diagram.order
      have jk' := (orderOld hs code (read hs code).2).mp jk
      exact (orderOld hs code (read hs code).2).mpr (st.trans i j k
        ((orderOld hs code (st.bound j k jk').1).mp ij) jk')
    · intro i j ij
      obtain ⟨k, s, v, hs, code, ij⟩ := (entries 0 i j).mp ij
      exact (read hs code).1.tree.tree.diagram.order.forward i j ij
    · intro i j k ik jk
      obtain ⟨s, v, hs, code⟩ := stage k (bound ik).2
      exact ((read hs code).1.tree.tree.diagram.order.chain i j k
        ((orderOld hs code (read hs code).2).mp ik) ((orderOld hs code (read hs code).2).mp jk)).imp
          (keeps hs code 0) (keeps hs code 0)
    · intro i j hj succ
      obtain ⟨s, v, hs, code⟩ := stage j hj
      have st := (read hs code).1.tree.tree.diagram.order
      obtain ⟨k, kj, pred⟩ := st.predecessor i j (read hs code).2 succ
      exact ⟨k, kj, fun l => (orderOld hs code (read hs code).2).trans
        ((pred l).trans (or_congr Iff.rfl (orderOld hs code (st.ordinal.transitive j (read hs code).2 k kj)).symm))⟩
    · intro δ hd limit
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) δ (hω.subset_limitOrdinal hZF limit δ hd)).elim
  have qdom : M.IsDomainOf I ω (U 1) := by
    intro i
    refine ⟨fun hi => ?_, fun ⟨a, ha⟩ => ?_⟩
    · obtain ⟨s, v, hs, code⟩ := stage i hi
      obtain ⟨a, ha⟩ := ((read hs code).1.tree.tree.diagram.model_domain i).mp (read hs code).2
      exact ⟨a, keeps hs code 1 ha⟩
    · obtain ⟨k, s, v, hs, code, ha⟩ := (entries 1 i a).mp ha
      exact hω.transitive hZF _ (finite hs code) i (((read hs code).1.tree.tree.diagram.model_domain i).mpr ⟨a, ha⟩)
  have oldFunction {B A X : M.Domain} (af : M.IsSetFunction I A) (bd : M.IsDomainOf I X B)
      (sub : M.MemberSubset B A) {i} (hi : M.mem i X) (x) : Rd_entry_d i x A ↔ Rd_entry_d i x B := by
    refine ⟨fun hx => ?_, fun ⟨p, pair, hp⟩ => ⟨p, pair, sub p hp⟩⟩
    obtain ⟨y, p, pair, hp⟩ := (bd i).mp hi
    exact af.2 i y x ⟨p, pair, sub p hp⟩ hx ▸ (show Rd_entry_d i y B from ⟨p, pair, hp⟩)
  have modelOld {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      {j} (hj : M.mem j (v 6)) (a) : Rd_entry_d j a (U 1) ↔ Rd_entry_d j a (v 9) :=
    oldFunction (functions 0) (read hs code).1.tree.tree.diagram.model_domain (inside hs code 1) hj a
  have pairMem {r i j B} (p : KPair_d M r i j) (h : Rd_entry_d i j B) : M.mem r B := by
    obtain ⟨q, qp, hq⟩ := h
    exact kpair_unique_l M hZF.1 qp p ▸ hq
  have maps i j g : It_map_d (U 2) i j g ↔ ∃ k s, ∃ v : Fin 64 → M.Domain,
      Rd_entry_d k s f ∧ Rt_tuple_d v s ∧ It_map_d (v 10) i j g := by
    refine ⟨fun ⟨r, pair, hr⟩ => ?_, fun ⟨k, s, v, hs, code, r, pair, hr⟩ => ?_⟩
    · obtain ⟨k, s, v, hs, code, hr⟩ := (entries 2 r g).mp hr
      exact ⟨k, s, v, hs, code, r, pair, hr⟩
    · exact ⟨r, pair, keeps hs code 2 hr⟩
  have gdom : M.IsDomainOf I (U 0) (U 2) := by
    intro r
    refine ⟨fun hr => ?_, fun ⟨g, hr⟩ => ?_⟩
    · obtain ⟨v, i, s, hs, code, hr⟩ := (us 0 r).mp hr
      obtain ⟨g, hg⟩ := ((read hs code).1.tree.tree.diagram.map_domain r).mp hr
      exact ⟨g, keeps hs code 2 hg⟩
    · obtain ⟨k, s, v, hs, code, hr⟩ := (entries 2 r g).mp hr
      exact inside hs code 0 r (((read hs code).1.tree.tree.diagram.map_domain r).mpr ⟨g, hr⟩)
  have mapBound {i j g} (hg : It_map_d (U 2) i j g) : Rd_entry_d i j (U 0) := by
    obtain ⟨r, pair, hr⟩ := hg
    exact ⟨r, pair, (gdom r).mpr ⟨g, hr⟩⟩
  have mapOld {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      {j k} (hk : M.mem k (v 6)) (g) : It_map_d (U 2) j k g ↔ It_map_d (v 10) j k g := by
    refine ⟨fun ⟨r, pair, hr⟩ => ?_, fun hg => (maps j k g).mpr ⟨i, s, v, hs, code, hg⟩⟩
    exact ⟨r, pair, (oldFunction (functions 1) (read hs code).1.tree.tree.diagram.map_domain (inside hs code 2)
      (pairMem pair ((orderOld hs code hk).mp (mapBound ⟨r, pair, hr⟩))) g).mp hr⟩
  have small {i j} {v : Fin 64 → M.Domain} (st : It_order_d (v 6) (v 8)) (hj : M.mem j (v 6))
      (ij : Rd_entry_d i j (U 0)) : M.mem i (v 6) := (order.forward i j ij).elim (fun eq => eq.symm ▸ hj) (st.ordinal.transitive j hj i)
  have diagram : It_diagram_d hZF ω ω (U 0) (U 1) (U 2) := by
    refine ⟨order, functions 0, qdom, ?_, functions 1, gdom, ?_, ?_, ?_⟩
    · intro i a ha
      obtain ⟨k, s, v, hs, code, ha⟩ := (entries 1 i a).mp ha
      exact (read hs code).1.tree.tree.diagram.models i a ha
    · intro i j g a X R b Y S hg ha hb ma mb
      obtain ⟨s, v, hs, code⟩ := stage j (bound (mapBound hg)).2
      have st := (read hs code).1.tree.tree.diagram
      exact st.elementary i j g a X R b Y S ((mapOld hs code (read hs code).2 g).mp hg)
        ((modelOld hs code (small st.order (read hs code).2 (mapBound hg)) a).mp ha)
        ((modelOld hs code (read hs code).2 b).mp hb) ma mb
    · intro i g hg x y hxy
      obtain ⟨k, s, v, hs, code, hg⟩ := (maps i i g).mp hg
      exact (read hs code).1.tree.tree.diagram.identity i g hg x y hxy
    · intro i j k a b d ha hb hd x y z hxy hyz
      obtain ⟨s, v, hs, code⟩ := stage k (bound (mapBound hb)).2
      have st := (read hs code).1.tree.tree.diagram
      exact st.comp i j k a b d ((mapOld hs code (small st.order (read hs code).2 (mapBound hb)) a).mp ha)
        ((mapOld hs code (read hs code).2 b).mp hb) ((mapOld hs code (read hs code).2 d).mp hd) x y z hxy hyz
  have sources i a (ha : Rd_entry_d i a (U 1)) : It_source_d hZF ω a := by
    obtain ⟨k, s, v, hs, code, ha⟩ := (entries 1 i a).mp ha
    exact (read hs code).1.tree.tree.sources i a ha
  have edom i : (∃ p, Rd_entry_d i p (U 3)) ↔ ∃ j, M.mem j ω ∧ M.SuccessorOf j i := by
    refine ⟨fun ⟨p, hp⟩ => ?_, fun ⟨j, hj, succ⟩ => ?_⟩
    · obtain ⟨k, s, v, hs, code, hp⟩ := (entries 3 i p).mp hp
      obtain ⟨j, hj, succ⟩ := ((read hs code).1.tree.tree.move_domain i).mp ⟨p, hp⟩
      exact ⟨j, hω.transitive hZF _ (finite hs code) j hj, succ⟩
    · obtain ⟨s, v, hs, code⟩ := stage j hj
      obtain ⟨p, hp⟩ := ((read hs code).1.tree.tree.move_domain i).mpr ⟨j, (read hs code).2, succ⟩
      exact ⟨p, keeps hs code 3 hp⟩
  have tree : It_tree_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) := by
    refine ⟨hω, diagram, ?_, sources, functions 2, edom, ?_, ?_⟩
    · intro e he
      obtain ⟨s, v, hs, code⟩ := stage e (num_mem_l hZF.1 hω (show Num_d 0 e from he))
      exact keeps hs code 1 ((read hs code).1.tree.tree.root e he)
    · intro i j hj succ
      obtain ⟨s, v, hs, code⟩ := stage j hj
      have st := (read hs code).1.tree
      obtain ⟨k, a, b, d, g, p, ⟨kj, pred⟩, ha, hb, hd, hg, hp, step⟩ := st.tree.steps i j (read hs code).2 succ
      refine ⟨k, a, b, d, g, p, ⟨kj, fun l => (orderOld hs code (read hs code).2).trans
        ((pred l).trans (or_congr Iff.rfl (orderOld hs code (st.tree.diagram.order.ordinal.transitive j (read hs code).2 k kj)).symm))⟩,
        keeps hs code 1 ha, keeps hs code 1 hb, keeps hs code 1 hd, (maps k j g).mpr ⟨j, s, v, hs, code, hg⟩,
        keeps hs code 3 hp, step⟩
    · intro δ hd limit
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) δ (hω.subset_limitOrdinal hZF limit δ hd)).elim
  have levels i ρ : Rd_entry_d i ρ (U 4) ↔ ∃ p κ F, Rd_entry_d i p (U 3) ∧ It_payload_d p κ ρ F := by
    refine ⟨fun hi => ?_, fun ⟨p, κ, F, hp, payload⟩ => ?_⟩
    · obtain ⟨k, s, v, hs, code, hi⟩ := (entries 4 i ρ).mp hi
      obtain ⟨p, κ, F, hp, payload⟩ := ((read hs code).1.tree.levels i ρ).mp hi
      exact ⟨p, κ, F, keeps hs code 3 hp, payload⟩
    · obtain ⟨k, s, v, hs, code, hp⟩ := (entries 3 i p).mp hp
      exact keeps hs code 4 (((read hs code).1.tree.levels i ρ).mpr ⟨p, κ, F, hp, payload⟩)
  refine ⟨U, ⟨tree, functions 3, levels, ?_, ?_⟩, functions 4, us⟩
  · intro i p κ ρ F a X R hp payload ha ma
    obtain ⟨k, s, v, hs, code, hp⟩ := (entries 3 i p).mp hp
    have st := (read hs code).1.tree
    obtain ⟨j, hj, succ⟩ := (st.tree.move_domain i).mp ⟨p, hp⟩
    exact st.exactness i p κ ρ F a X R hp payload
      ((modelOld hs code (st.tree.diagram.order.ordinal.transitive j hj i succ.predecessor_mem) a).mp ha) ma
  · intro i j ρ μ hi hj ij
    obtain ⟨k, s, v, hs, ps, p, pair, hp⟩ := (entries 4 i ρ).mp hi
    obtain ⟨l, t, w, ht, pt, q, qp, hq⟩ := (entries 4 j μ).mp hj
    obtain ⟨m, r, u, hr, pr, su, tu⟩ := merge hs ht ps pt
    exact (read hr pr).1.tree.increasing i j ρ μ ⟨p, pair, su.2.2.1 4 p hp⟩ ⟨q, qp, tu.2.2.1 4 q hq⟩ ij

end YesMetaZFC.SetTheory.LargeCardinal
