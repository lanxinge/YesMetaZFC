import YesMetaZFC.SetTheory.LargeCardinal.IterationCopySequence
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # 相容有限复制历史的并

三张实际图取并后仍为函数。每个旧定义域上的限制恰为原图，因此所有
有限元条件在包含其指标的同一阶段验证，得到长度 ω 的完整复制图列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def ic_pick {A : Type u} (H Q G : A) : Fin 3 → A := Fin.cases H (Fin.cases Q (fun _ => G))
private def Ic_union_d (a : Fin 3) (f x : M.Domain) : Prop := ∃ i s H S Q G,
  Rd_entry_d i s f ∧ Rd_quad_d s H S Q G ∧ M.mem x (ic_pick H Q G a)
private def ic_union_m (a : Fin 3) {d} (f x : Term d) : Formula 1 d := set[d] ⟪
  ∃ i s H S Q G, ⌜rd_entry0_m⌝ₚ(i, s, ⌜f⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(s, H, S, Q, G) ∧
    ⌜(fun H Q G x => (Definitional.Formula.mem x (ic_pick H Q G a) : Formula 1 _))⌝ₚ(H, Q, G, ⌜x⌝ₛ)⟫
@[simp] private theorem ic_union_closed_l (a : Fin 3) {d} (f x : Term d)
    (hf : f.freeSupport = []) (hx : x.freeSupport = []) : (ic_union_m a f x).FreeClosed := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) a <;>
    simp -implicitDefEqProofs [ic_union_m, ic_pick, Definitional.Formula.FreeClosed, hf, hx] <;> rfl
private theorem ic_union_sat_l (hE : Extensional M) (a : Fin 3) {d} (η : Env M d) (f x : Term d) :
    Formula.satisfies η (ic_union_m a f x) ↔ Ic_union_d a (f.eval η) (x.eval η) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) a <;>
    simp only [ic_union_m, Ic_union_d, ic_pick, Fin.cases_zero, Fin.cases_succ,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      rd_entry0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken] <;> rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ic_sequence_union_l {ω T Q G E L D f : M.Domain} (hω : M.IsOmega ω)
    (original : It_diagram_d hZF ω ω T Q G) (fn : Fn0_d ω D f)
    (valid : ∀ i s, Rd_entry_d i s f → Ic_state_d hZF ω T Q G E L i s)
    (chain : ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s f → Rd_entry_d j t f → Ic_extend_d s t) :
    ∃ H Q' G', Ic_history_d hZF ω T Q G E L ω H T Q' G' ∧
      ∀ i s H₀ S₀ Q₀ G₀, Rd_entry_d i s f → Rd_quad_d s H₀ S₀ Q₀ G₀ →
        M.MemberSubset H₀ H ∧ M.MemberSubset Q₀ Q' ∧ M.MemberSubset G₀ G' := by
  have ff := fn0_function_l (ZF.modelsKP hZF) fn
  have read {i s H S Q' G'} (hs : Rd_entry_d i s f) (hp : Rd_quad_d s H S Q' G') :
      ∃ m, M.SuccessorOf m i ∧ Ic_history_d hZF ω T Q G E L m H S Q' G' := by
    obtain ⟨m, A, B, C, D, hm, pack, hist⟩ := valid i s hs
    obtain ⟨e₁, e₂, e₃, e₄⟩ := pack.unique_l hp
    subst A B C D
    exact ⟨m, hm, hist⟩
  let η : Env M 0 := ⟨Fin.elim0, fun _ => f⟩
  let φ : BinarySchema 0 := { body := ic_extend_m (.bound 1) .newest }
  have sat s t : φ.denote η s t ↔ Ic_extend_d s t := ic_extend_sat_l hZF.1 ..
  have increasing := ZF.rel_chain_l I hZF φ η hω ff
    (fun _ _ _ _ _ _ h g => (sat _ _).mpr (((sat _ _).mp h).trans_l ((sat _ _).mp g)))
    (fun i j s t hij hs ht => (sat s t).mpr (chain i j s t hij hs ht))
  have self {i s} (hs : Rd_entry_d i s f) : Ic_extend_d s s := by
    obtain ⟨_, H, S, Q', G', _, hp, _⟩ := valid i s hs
    exact ⟨H, S, Q', G', H, S, Q', G', hp, hp, fun _ h => h, fun _ h => h, fun _ h => h⟩
  have merge {i j s t} (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) :
      ∃ k v, Rd_entry_d k v f ∧ Ic_extend_d s v ∧ Ic_extend_d t v := by
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare i (fn.bound_l hs).1 j (fn.bound_l ht).1 with eq | lt | gt
    · have eq := hZF.1.eq_of_same_members i j eq
      subst j
      have eq := ff.1.2 i t s ht hs
      subst t
      exact ⟨i, s, hs, self hs, self hs⟩
    · exact ⟨j, t, ht, (sat s t).mp (increasing i j s t lt hs ht), self ht⟩
    · exact ⟨i, s, hs, self hs, (sat t s).mp (increasing j i t s gt ht hs)⟩
  have part {m H S Q' G'} (hist : Ic_history_d hZF ω T Q G E L m H S Q' G') (a : Fin 3) :
      M.IsSetFunction I (ic_pick H Q' G' a) :=
    Fin.cases hist.function (Fin.cases hist.diagram.model_function (fun _ => hist.diagram.map_function)) a
  have keep {s t H S Q' G' H' S' Q'' G''} (ext : Ic_extend_d s t)
      (hs : Rd_quad_d s H S Q' G') (ht : Rd_quad_d t H' S' Q'' G'') (a : Fin 3) :
      M.MemberSubset (ic_pick H Q' G' a) (ic_pick H' Q'' G'' a) := by
    obtain ⟨hh, hq, hg⟩ := ext.read_l hs ht
    exact Fin.cases hh (Fin.cases hq (fun _ => hg)) a
  -- 传递闭包只给本次分离提供集合界；它不限制复制模型的高度。
  obtain ⟨U, tu, hDU, _⟩ := ZF.tc_exists_l I hZF D
  have owned {i s H S Q' G'} (hs : Rd_entry_d i s f) (pack : Rd_quad_d s H S Q' G') (a : Fin 3) :
      M.mem (ic_pick H Q' G' a) U := by
    obtain ⟨p, hp, q, hq, hr⟩ := pack
    obtain ⟨hH, hqU⟩ := hr.mem_l M tu (tu D hDU s (fn.bound_l hs).2)
    have hpU := (hq.mem_l M tu hqU).2
    obtain ⟨hQ, hG⟩ := hp.mem_l M tu hpU
    exact Fin.cases hH (Fin.cases hQ (fun _ => hG)) a
  have collect (a : Fin 3) : ∃ B, ∀ x, M.mem x B ↔ Ic_union_d a f x := by
    let ψ : UnarySchema 1 := { body := ic_union_m a (.bound 1) .newest }
    let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
    obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF ψ ρ U
    refine ⟨B, fun x => (hb x).trans ?_⟩
    change (M.mem x U ∧ ψ.denote ρ x) ↔ _
    rw [show ψ.denote ρ x ↔ Ic_union_d a f x from ic_union_sat_l hZF.1 a ..]
    exact ⟨And.right, fun h => ⟨by obtain ⟨i, s, H, S, Q', G', hs, hp, hx⟩ := h; exact tu _ (owned hs hp a) x hx, h⟩⟩
  have graphs (a : Fin 3) {B} (bs : ∀ x, M.mem x B ↔ Ic_union_d a f x) :
      M.IsSetFunction I B ∧ ∀ x y, Rd_entry_d x y B ↔ ∃ i s H S Q' G',
        Rd_entry_d i s f ∧ Rd_quad_d s H S Q' G' ∧ Rd_entry_d x y (ic_pick H Q' G' a) := by
    have entries x y : Rd_entry_d x y B ↔ ∃ i s H S Q' G',
        Rd_entry_d i s f ∧ Rd_quad_d s H S Q' G' ∧ Rd_entry_d x y (ic_pick H Q' G' a) := by
      refine ⟨fun ⟨p, pair, hp⟩ => ?_, fun ⟨i, s, H, S, Q', G', hs, pack, p, pair, hp⟩ => ?_⟩
      · obtain ⟨i, s, H, S, Q', G', hs, pack, hp⟩ := (bs p).mp hp
        exact ⟨i, s, H, S, Q', G', hs, pack, p, pair, hp⟩
      · exact ⟨p, pair, (bs p).mpr ⟨i, s, H, S, Q', G', hs, pack, hp⟩⟩
    refine ⟨⟨fun p hp => ?_, fun x y z hy hz => ?_⟩, entries⟩
    · obtain ⟨i, s, H, S, Q', G', hs, pack, hp⟩ := (bs p).mp hp
      obtain ⟨m, _, hist⟩ := read hs pack
      exact (part hist a).1 p hp
    · obtain ⟨i, s, H, S, Q', G', hs, pack, hy⟩ := (entries x y).mp hy
      obtain ⟨j, t, H', S', Q'', G'', ht, pack', hz⟩ := (entries x z).mp hz
      obtain ⟨k, v, hv, sv, tv⟩ := merge hs ht
      obtain ⟨m, A, B, C, D, _, vp, vh⟩ := valid k v hv
      obtain ⟨p, pair, hp⟩ := hy
      obtain ⟨q, qp, hq⟩ := hz
      exact (part vh a).2 x y z ⟨p, pair, keep sv pack vp a p hp⟩ ⟨q, qp, keep tv pack' vp a q hq⟩
  obtain ⟨H, hs⟩ := collect 0
  obtain ⟨Q', qs⟩ := collect 1
  obtain ⟨G', gs⟩ := collect 2
  obtain ⟨hf, he⟩ := graphs 0 hs
  obtain ⟨qf, qe⟩ := graphs 1 qs
  obtain ⟨gf, ge⟩ := graphs 2 gs
  have inside {i s H₀ S₀ Q₀ G₀} (h : Rd_entry_d i s f) (hp : Rd_quad_d s H₀ S₀ Q₀ G₀) :
      M.MemberSubset H₀ H ∧ M.MemberSubset Q₀ Q' ∧ M.MemberSubset G₀ G' :=
    ⟨fun x hx => (hs x).mpr ⟨i, s, H₀, S₀, Q₀, G₀, h, hp, hx⟩,
      fun x hx => (qs x).mpr ⟨i, s, H₀, S₀, Q₀, G₀, h, hp, hx⟩,
      fun x hx => (gs x).mpr ⟨i, s, H₀, S₀, Q₀, G₀, h, hp, hx⟩⟩
  have below {i m j} (hi : M.mem i ω) (hm : M.SuccessorOf m i) (hj : M.mem j m) : M.mem j ω :=
    ((hm j).mp hj).elim (hω.transitive hZF i hi j) (fun eq => (hZF.1.eq_of_same_members j i eq).symm ▸ hi)
  have hdom : M.IsDomainOf I ω H := by
    intro i
    constructor
    · intro hi
      obtain ⟨s, _, hsi⟩ := fn.2.1 i hi
      obtain ⟨m, A, B, C, D, hm, pack, hist⟩ := valid i s hsi
      obtain ⟨r, hr⟩ := (hist.domain i).mp hm.predecessor_mem
      exact ⟨r, (he i r).mpr ⟨i, s, A, B, C, D, hsi, pack, hr⟩⟩
    · rintro ⟨r, hr⟩
      obtain ⟨j, s, A, B, C, D, hj, pack, hr⟩ := (he i r).mp hr
      obtain ⟨m, hm, hist⟩ := read hj pack
      exact below (fn.bound_l hj).1 hm ((hist.domain i).mpr ⟨r, hr⟩)
  have qdom : M.IsDomainOf I ω Q' := by
    intro i
    constructor
    · intro hi
      obtain ⟨s, _, hsi⟩ := fn.2.1 i hi
      obtain ⟨m, A, B, C, D, hm, pack, hist⟩ := valid i s hsi
      obtain ⟨r, hr⟩ := (hist.diagram.model_domain i).mp hm.predecessor_mem
      exact ⟨r, (qe i r).mpr ⟨i, s, A, B, C, D, hsi, pack, hr⟩⟩
    · rintro ⟨r, hr⟩
      obtain ⟨j, s, A, B, C, D, hj, pack, hr⟩ := (qe i r).mp hr
      obtain ⟨m, hm, hist⟩ := read hj pack
      exact below (fn.bound_l hj).1 hm ((hist.diagram.model_domain i).mpr ⟨r, hr⟩)
  have pair_mem {r i j A} (pair : KPair_d M r i j) (hr : Rd_entry_d i j A) : M.mem r A := by
    obtain ⟨q, hq, hqA⟩ := hr
    exact kpair_unique_l M hZF.1 hq pair ▸ hqA
  have gdom : M.IsDomainOf I T G' := by
    intro r
    constructor
    · intro hr
      obtain ⟨i, j, pair⟩ := original.order.relation r hr
      have hj := (original.order.bound i j ⟨r, pair, hr⟩).2
      obtain ⟨s, _, hjs⟩ := fn.2.1 j hj
      obtain ⟨m, A, B, C, D, hm, pack, hist⟩ := valid j s hjs
      obtain ⟨g, hg⟩ := (hist.diagram.map_domain r).mp (pair_mem pair ((hist.order i j).mpr ⟨⟨r, pair, hr⟩, hm.predecessor_mem⟩))
      exact ⟨g, (ge r g).mpr ⟨j, s, A, B, C, D, hjs, pack, hg⟩⟩
    · rintro ⟨g, hg⟩
      obtain ⟨j, s, A, B, C, D, hj, pack, hg⟩ := (ge r g).mp hg
      obtain ⟨m, _, hist⟩ := read hj pack
      obtain ⟨i, k, pair⟩ := hist.diagram.order.relation r ((hist.diagram.map_domain r).mpr ⟨g, hg⟩)
      exact pair_mem pair ((hist.order i k).mp ⟨r, pair, (hist.diagram.map_domain r).mpr ⟨g, hg⟩⟩).1
  have map_bound {i j g} (hg : It_map_d G' i j g) : Rd_entry_d i j T := by
    obtain ⟨r, pair, hr⟩ := hg
    exact ⟨r, pair, (gdom r).mpr ⟨g, hr⟩⟩
  have recover {A B C} (af : M.IsSetFunction I A) (bd : M.IsDomainOf I C B) (sub : M.MemberSubset B A)
      {i} (hi : M.mem i C) (x) : Rd_entry_d i x A ↔ Rd_entry_d i x B := by
    refine ⟨fun h => ?_, fun ⟨p, pair, hp⟩ => ⟨p, pair, sub p hp⟩⟩
    obtain ⟨y, hy⟩ := (bd i).mp hi
    obtain ⟨p, pair, hp⟩ := hy
    exact af.2 i y x ⟨p, pair, sub p hp⟩ h ▸ (show Rd_entry_d i y B from ⟨p, pair, hp⟩)
  -- 任一有限阶段都恰为三张并图在其旧定义域上的限制。
  have stage i (hi : M.mem i ω) : ∃ m A B C D, M.SuccessorOf m i ∧ Ic_history_d hZF ω T Q G E L m A B C D ∧
      (∀ j, M.mem j m → ∀ r, Rd_entry_d j r H ↔ Rd_entry_d j r A) ∧
      (∀ j, M.mem j m → ∀ r, Rd_entry_d j r Q' ↔ Rd_entry_d j r C) ∧
      ∀ k j, M.mem j m → ∀ g, It_map_d G' k j g ↔ It_map_d D k j g := by
    obtain ⟨s, _, his⟩ := fn.2.1 i hi
    obtain ⟨m, A, B, C, D, hm, pack, hist⟩ := valid i s his
    obtain ⟨ah, cq, dg⟩ := inside his pack
    refine ⟨m, A, B, C, D, hm, hist, fun j hj r => recover hf hist.domain ah hj r,
      fun j hj r => recover qf hist.diagram.model_domain cq hj r, ?_⟩
    intro k j hj g
    refine ⟨fun hg => ?_, fun ⟨r, pair, hr⟩ => ⟨r, pair, (recover gf hist.diagram.map_domain dg
      ((hist.diagram.map_domain r).mpr ⟨g, hr⟩) g).mpr hr⟩⟩
    obtain ⟨r, pair, hr⟩ := hg
    exact ⟨r, pair, (recover gf hist.diagram.map_domain dg
      (pair_mem pair ((hist.order k j).mpr ⟨map_bound ⟨r, pair, hr⟩, hj⟩)) g).mp hr⟩
  have small {i j m} (hm : M.SuccessorOf m j) (hij : Rd_entry_d i j T) : M.mem i m :=
    (original.order.forward i j hij).elim (fun eq => eq.symm ▸ hm.predecessor_mem) (fun hi => (hm i).mpr (Or.inl hi))
  have diagram : It_diagram_d hZF ω ω T Q' G' := by
    refine ⟨original.order, qf, qdom, ?_, gf, gdom, ?_, ?_, ?_⟩
    · intro i c hc
      obtain ⟨m, A, B, C, D, hm, hist, _, q, _⟩ := stage i ((qdom i).mpr ⟨c, hc⟩)
      exact hist.diagram.models i c ((q i hm.predecessor_mem c).mp hc)
    · intro i j g c X R d Y S hg hc hd mx my
      have hij := map_bound hg
      obtain ⟨m, A, B, C, D, hm, hist, _, q, maps⟩ := stage j (original.order.bound i j hij).2
      exact hist.diagram.elementary i j g c X R d Y S ((maps i j hm.predecessor_mem g).mp hg)
        ((q i (small hm hij) c).mp hc) ((q j hm.predecessor_mem d).mp hd) mx my
    · intro i g hg x y hxy
      obtain ⟨m, A, B, C, D, hm, hist, _, _, maps⟩ := stage i (original.order.bound i i (map_bound hg)).1
      exact hist.diagram.identity i g ((maps i i hm.predecessor_mem g).mp hg) x y hxy
    · intro i j k f g h hf hg hh x y z hxy hyz
      have hjk := map_bound hg
      obtain ⟨m, A, B, C, D, hm, hist, _, _, maps⟩ := stage k (original.order.bound j k hjk).2
      exact hist.diagram.comp i j k f g h ((maps i j (small hm hjk) f).mp hf)
        ((maps j k hm.predecessor_mem g).mp hg) ((maps i k hm.predecessor_mem h).mp hh) x y z hxy hyz
  have at_stage {i m A X P π z Z α} (h : ∀ j, M.mem j m → ∀ r, Rd_entry_d j r H ↔ Rd_entry_d j r A) (hi : M.mem i m) :
      Ic_at_d H i X P π z Z α ↔ Ic_at_d A i X P π z Z α :=
    exists_congr fun r => and_congr (h i hi r) Iff.rfl
  refine ⟨H, Q', G', ⟨diagram, fun i j => ⟨fun hij => ⟨hij, (original.order.bound i j hij).2⟩, And.left⟩,
    hf, hdom, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ _ _ _ _ hs hp => inside hs hp⟩
  · intro i r hr
    obtain ⟨m, A, B, C, D, hm, hist, h, q, _⟩ := stage i ((hdom i).mpr ⟨r, hr⟩)
    obtain ⟨c, X, P, π, z, Z, α, cell, hc, hz, row⟩ := hist.rows i r ((h i hm.predecessor_mem r).mp hr)
    exact ⟨c, X, P, π, z, Z, α, cell, hc, (q i hm.predecessor_mem z).mpr hz, row⟩
  · intro i j X A π z Z α Y B σ u U β ai aj hij
    obtain ⟨r, hr, _⟩ := aj
    obtain ⟨m, C, S, Q₀, G₀, hm, hist, h, _, _⟩ := stage j ((hdom j).mpr ⟨r, hr⟩)
    exact hist.past i j X A π z Z α Y B σ u U β ((at_stage h ((hm i).mpr (Or.inl hij))).mp ai)
      ((at_stage h hm.predecessor_mem).mp ⟨r, hr, ‹Ic_cell_d r Y B σ u U β›⟩) hij
  · intro i j X A π z Z α Y B σ u U β g ai aj hg
    have hij := map_bound hg
    obtain ⟨m, C, S, Q₀, G₀, hm, hist, h, _, maps⟩ := stage j (original.order.bound i j hij).2
    exact hist.cuts i j X A π z Z α Y B σ u U β g ((at_stage h (small hm hij)).mp ai)
      ((at_stage h hm.predecessor_mem).mp aj) ((maps i j hm.predecessor_mem g).mp hg)
  · intro i j X A π z Z α Y B σ u U β g k ai aj hg hk
    have hij := map_bound hk
    obtain ⟨m, C, S, Q₀, G₀, hm, hist, h, _, maps⟩ := stage j (original.order.bound i j hij).2
    exact hist.squares i j X A π z Z α Y B σ u U β g k
      ((at_stage h (small hm hij)).mp ai) ((at_stage h hm.predecessor_mem).mp aj)
      hg ((maps i j hm.predecessor_mem k).mp hk)
  · intro i j k N B σ u U β X A π z Z α P C τ v V γ p κ ρ F g succ pred ai ak aj hp pay hg
    obtain ⟨m, A₀, S, Q₀, G₀, hm, hist, h, _, maps⟩ := stage j (original.order.bound k j (map_bound hg)).2
    exact hist.steps i j k N B σ u U β X A π z Z α P C τ v V γ p κ ρ F g succ pred
      ((at_stage h ((hm i).mpr (Or.inl succ.predecessor_mem))).mp ai)
      ((at_stage h ((hm k).mpr (Or.inl pred.1))).mp ak) ((at_stage h hm.predecessor_mem).mp aj)
      hp pay ((maps k j hm.predecessor_mem g).mp hg)
  · intro i j p succ hj hp empty
    obtain ⟨m, A, B, C, D, hm, hist, h, _, maps⟩ := stage j hj
    have hi := (hm i).mpr (Or.inl succ.predecessor_mem)
    obtain ⟨same, ident⟩ := hist.pads i j p succ hm.predecessor_mem hp empty
    exact ⟨fun r => (h i hi r).trans ((same r).trans (h j hm.predecessor_mem r).symm),
      fun f x y hf => ident f x y ((maps i j hm.predecessor_mem f).mp hf)⟩

end YesMetaZFC.SetTheory.LargeCardinal
