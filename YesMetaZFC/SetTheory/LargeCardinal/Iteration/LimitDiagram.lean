import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail

/-! # 在极限长度上沿共尾树枝添入新顶点 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
include hKP

theorem it_limit_order_l {α T B : M.Domain} (h : It_order_d α T)
    (hl : M.IsLimitOrdinal α) (b : It_branch_d α T B) : ∃ β U, M.SuccessorOf β α ∧ It_order_d β U ∧
      ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B) := by
  obtain ⟨β, hβ⟩ := KP.exists_successor hKP α
  have no : ¬ M.mem α α := fun ha => h.ordinal.wellOrder.linear.irrefl α ha ha
  have sc i : M.mem i β ↔ M.mem i α ∨ i = α := (hβ i).trans
    (or_congr Iff.rfl ⟨hKP.1.eq_of_same_members i α, fun e => e ▸ fun _ => Iff.rfl⟩)
  let ρ : Env M 3 := ⟨Fin.cases α (Fin.cases B (fun _ => T)), fun _ => α⟩
  let φ : Delta0BinarySchema 3 := {
    body := .disj (rd_entry0_m (.bound 1) .newest (.bound 4))
      (.conj (Formula.extensionalEq .newest (.bound 2))
        (.disj (Formula.extensionalEq (.bound 1) (.bound 2)) (.mem (.bound 1) (.bound 3))))
    delta0 := .disj (rd_entry0_delta_l ..) (.conj (.atom _ _ _) (.disj (.atom _ _ _) (.mem _ _))) }
  have sat i j : φ.toBinarySchema.denote ρ i j ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨U, ur⟩ := rw_rel_exists_l hKP φ ρ β
  have us i j := ur.entry_l hKP (x := i) (y := j)
  have bound i j (hr : Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B)) : M.mem i β ∧ M.mem j β := by
    rcases hr with hr | ⟨rfl, rfl | hi⟩
    · exact ⟨(sc i).mpr (Or.inl (h.bound i j hr).1), (sc j).mpr (Or.inl (h.bound i j hr).2)⟩
    · exact ⟨hβ.predecessor_mem, hβ.predecessor_mem⟩
    · exact ⟨(sc i).mpr (Or.inl (b.subset i hi)), hβ.predecessor_mem⟩
  have read i j : Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B) :=
    (us i j).trans ⟨fun hh => (sat i j).mp hh.2.2,
      fun hh => ⟨(bound i j hh).1, (bound i j hh).2, (sat i j).mpr hh⟩⟩
  have old i j (hj : M.mem j α) : Rd_entry_d i j U ↔ Rd_entry_d i j T := (read i j).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have tip i : Rd_entry_d i α U ↔ i = α ∨ M.mem i B := (read i α).trans
    ⟨fun hh => hh.elim (fun hh => (no (h.bound i α hh).2).elim) And.right, fun hh => Or.inr ⟨rfl, hh⟩⟩
  have bounds i j (hij : Rd_entry_d i j U) := bound i j ((read i j).mp hij)
  refine ⟨β, U, hβ, ⟨KP.successor_isOrdinal hKP h.ordinal hβ, fun p hp => ?_, bounds,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, read⟩
  · obtain ⟨i, _, j, _, hp, _⟩ := (ur p).mp hp
    exact ⟨i, j, hp⟩
  · intro i hi
    rcases (sc i).mp hi with hi | rfl
    · exact (read i i).mpr (Or.inl (h.refl i hi))
    · exact (tip _).mpr (Or.inl rfl)
  · intro i j k hij hjk
    rcases (sc k).mp (bounds j k hjk).2 with hk | rfl
    · have hjk := (old j k hk).mp hjk
      exact (old i k hk).mpr (h.trans i j k ((old i j (h.bound j k hjk).1).mp hij) hjk)
    · rcases (tip j).mp hjk with rfl | hj
      · exact hij
      · exact (tip i).mpr (Or.inr (b.down i j ((old i j (b.subset j hj)).mp hij) hj))
  · intro i j hij
    rcases (read i j).mp hij with hij | ⟨rfl, rfl | hi⟩
    · exact h.forward i j hij
    · exact Or.inl rfl
    · exact Or.inr (b.subset i hi)
  · intro i j k hik hjk
    rcases (sc k).mp (bounds i k hik).2 with hk | rfl
    · exact (h.chain i j k ((old i k hk).mp hik) ((old j k hk).mp hjk)).imp
        (fun hh => (read i j).mpr (Or.inl hh)) (fun hh => (read j i).mpr (Or.inl hh))
    · rcases (tip i).mp hik with rfl | hi
      · exact Or.inr hjk
      · rcases (tip j).mp hjk with rfl | hj
        · exact Or.inl hik
        · exact (b.chain i j hi hj).imp (fun hh => (read i j).mpr (Or.inl hh)) (fun hh => (read j i).mpr (Or.inl hh))
  · intro i j hj hs
    rcases (sc j).mp hj with hj | rfl
    · obtain ⟨k, hk, pred⟩ := h.predecessor i j hj hs
      exact ⟨k, hk, fun l => (old l j hj).trans ((pred l).trans
        (or_congr Iff.rfl (old l k (h.ordinal.transitive j hj k hk)).symm))⟩
    · exact (it_successor_not_limit_l hKP.1 (h.ordinal.mem hs.predecessor_mem) hs hl).elim
  · intro δ hδ limit i hi
    rcases (sc δ).mp hδ with hδ | rfl
    · obtain ⟨j, hj, hjδ, above⟩ := h.cofinal δ hδ limit i hi
      exact ⟨j, hj, (old j δ hδ).mpr hjδ, above⟩
    · obtain ⟨j, hj, above⟩ := b.cofinal i hi
      exact ⟨j, b.subset j hj, (tip j).mpr (Or.inr hj), above⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限处新增的整列嵌入图

旧箭头保持原值，枝上的新箭头读取已构造的极限投影列，新对角线取恒等。
三种定义域互斥，故替代给出真实函数图及精确的双向读取式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_finish_d (α G P e i j f : M.Domain) : Prop := It_map_d G i j f ∨
  j = α ∧ ((i = α ∧ f = e) ∨ Rd_entry_d i f P)
def it_finish_m {d} (α G P e i j f : Term d) : Formula 1 d := .disj (it_map_m G i j f)
  (.conj (Formula.extensionalEq j α) (.disj (.conj (Formula.extensionalEq i α) (Formula.extensionalEq f e))
    (rd_entry_m i f P)))
derive_free_closed it_finish_m

theorem it_finish_sat_l (hE : Extensional M) {d} (ρ : Env M d) (α G P e i j f : Term d) :
    Formula.satisfies ρ (it_finish_m α G P e i j f) ↔
      It_finish_d (α.eval ρ) (G.eval ρ) (P.eval ρ) (e.eval ρ) (i.eval ρ) (j.eval ρ) (f.eval ρ) := by
  simp only [it_finish_m, It_finish_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, it_map_sat_l hE, rd_entry_sat_l hE]

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_finish_unique_l {ω α T Q G B d N W P e i j f g : M.Domain}
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (inside : M.MemberSubset B α) (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P)
    (hf : It_finish_d α G P e i j f) (hg : It_finish_d α G P e i j g) : f = g := by
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  have right {k f} (hf : It_map_d G k α f) : False := no (h.order.bound k α (h.map_bound_l hZF hf)).2
  have tip {f} (hf : Rd_entry_d α f P) : False := no (inside α ((cone.domain α).mpr ⟨f, hf⟩))
  rcases hf with hf | ⟨rfl, ⟨rfl, rfl⟩ | hf⟩
  · rcases hg with hg | ⟨rfl, _⟩
    · exact h.map_unique_l hZF hf hg
    · exact (right hf).elim
  · rcases hg with hg | ⟨_, ⟨_, eq⟩ | hg⟩
    · exact (right hg).elim
    · exact eq.symm
    · exact (tip hg).elim
  · rcases hg with hg | ⟨_, ⟨rfl, _⟩ | hg⟩
    · exact (right hg).elim
    · exact (tip hf).elim
    · exact cone.function.2 i f g hf hg

theorem it_finish_maps_l {ω α T Q G B d N W P e U : M.Domain}
    (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (inside : M.MemberSubset B α) (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P)
    (us : ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B))
    (rel : M.IsSetRelation I U) : ∃ H, M.IsSetFunction I H ∧ M.IsDomainOf I U H ∧
      ∀ i j f, It_map_d H i j f ↔ It_finish_d α G P e i j f := by
  let ρ : Env M 4 := ⟨Fin.cases α (Fin.cases G (Fin.cases P (fun _ => e))), fun _ => α⟩
  let φ : BinarySchema 4 := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 3) (.bound 1) .newest)
      (it_finish_m (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 1) .newest (.bound 2)))) }
  have sat r f : φ.denote ρ r f ↔ ∃ i j, KPair_d M r i j ∧ It_finish_d α G P e i j f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, it_finish_sat_l hZF.1]; rfl
  have total r (hr : M.mem r U) : ∃ f, φ.denote ρ r f := by
    obtain ⟨i, j, hp⟩ := rel r hr
    rcases (us i j).mp ⟨r, hp, hr⟩ with hij | ⟨rfl, rfl | hi⟩
    · obtain ⟨f, hf⟩ := h.map_l hZF hij
      exact ⟨f, (sat r f).mpr ⟨i, j, hp, Or.inl hf⟩⟩
    · exact ⟨e, (sat r e).mpr ⟨_, _, hp, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩⟩
    · obtain ⟨f, hf⟩ := (cone.domain i).mp hi
      exact ⟨f, (sat r f).mpr ⟨_, _, hp, Or.inr ⟨rfl, Or.inr hf⟩⟩⟩
  have unique r f g (hf : φ.denote ρ r f) (hg : φ.denote ρ r g) : f = g := by
    obtain ⟨i, j, hp, hf⟩ := (sat r f).mp hf
    obtain ⟨i', j', hp', hg⟩ := (sat r g).mp hg
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    exact it_finish_unique_l hZF h inside cone hf hg
  obtain ⟨D, hd⟩ := ZF.exists_functionalImage hZF φ ρ U total unique
  obtain ⟨H, hh, hs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun r _ => unique r)
    (fun r f hr hf => (hd f).mpr ⟨r, hr, hf⟩)
  refine ⟨H, hh.1, hh.2.1, fun i j f => ⟨?_, ?_⟩⟩
  · rintro ⟨r, hp, hrf⟩
    obtain ⟨i', j', hp', hf⟩ := (sat r f).mp ((hs r f).mp hrf).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    exact hf
  · intro hf
    obtain ⟨r, hp⟩ := (I).total i j
    have hij : Rd_entry_d i j U := by
      apply (us i j).mpr
      rcases hf with hf | ⟨rfl, ⟨rfl, _⟩ | hf⟩
      · exact Or.inl (h.map_bound_l hZF hf)
      · exact Or.inr ⟨rfl, Or.inl rfl⟩
      · exact Or.inr ⟨rfl, Or.inr ((cone.domain i).mpr ⟨f, hf⟩)⟩
    obtain ⟨t, ht, htU⟩ := hij
    exact ⟨r, hp, (hs r f).mpr ⟨kpair_unique_l M hZF.1 ht hp ▸ htU, (sat r f).mpr ⟨i, j, hp, hf⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限添枝后的完整初等图与交换律 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_limit_diagram_l {ω α T Q G B d N W P : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (hl : M.IsLimitOrdinal α)
    (b : It_branch_d α T B) (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P) :
    ∃ β U Q' G' e, M.SuccessorOf β α ∧ It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' ∧
      (∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B)) ∧
      (∀ i c, Rd_entry_d i c Q' ↔ Rd_entry_d i c Q ∨ i = α ∧ c = d) ∧
      ∀ i j f, It_map_d G' i j f ↔ It_finish_d α G P e i j f := by
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  obtain ⟨β, U, hβ, order, us⟩ := it_limit_order_l (ZF.modelsKP hZF) h.order hl b
  obtain ⟨Q', qf, qs⟩ := Structure.IsSequenceOfLength.exists_append (value := d) (ZF.modelsKP hZF) I
    ⟨h.order.ordinal, h.model_function, h.model_domain⟩ order.ordinal hβ
  have qold i c (hi : M.mem i α) : Rd_entry_d i c Q' ↔ Rd_entry_d i c Q := (qs i c).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have qtip c : Rd_entry_d α c Q' ↔ c = d := (qs α c).trans
    ⟨fun hh => hh.elim (fun hh => (no ((h.model_domain α).mpr ⟨c, hh⟩)).elim) And.right,
      fun hh => Or.inr ⟨rfl, hh⟩⟩
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (c := d) (X := N) hω
  obtain ⟨G', gf, gd, gs⟩ := it_finish_maps_l hZF h b.subset cone (e := e) us order.relation
  have gold i j f (hj : M.mem j α) : It_map_d G' i j f ↔ It_map_d G i j f := (gs i j f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have typed i j f c X R c' Y S (hf : It_map_d G' i j f) (hc : Rd_entry_d i c Q') (hc' : Rd_entry_d j c' Q')
      (mx : Smdl_d I c X R) (my : Smdl_d I c' Y S) : Smap_d I ω c c' X Y f := by
    rcases (gs i j f).mp hf with hf | ⟨rfl, ⟨rfl, rfl⟩ | hf⟩
    · have hij := h.order.bound i j (h.map_bound_l hZF hf)
      exact h.elementary i j f c X R c' Y S hf ((qold i c hij.1).mp hc) ((qold j c' hij.2).mp hc') mx my
    · have eq := (qtip c).mp hc
      have eq' := (qtip c').mp hc'
      subst c c'
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx cone.model
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I my cone.model
      exact he
    · have eq := (qtip c').mp hc'
      subst c'
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I my cone.model
      exact cone.elementary i f c X R hf ((qold i c (b.subset i ((cone.domain i).mpr ⟨f, hf⟩))).mp hc) mx
  have ident i f (hf : It_map_d G' i i f) x y (hxy : Rd_entry_d x y f) : x = y := by
    rcases (gs i i f).mp hf with hf | ⟨rfl, ⟨_, rfl⟩ | hf⟩
    · exact h.identity i f hf x y hxy
    · exact ((es x y).mp hxy).2
    · exact (no (b.subset _ ((cone.domain _).mpr ⟨f, hf⟩))).elim
  have commute i j k f g v (hf : It_map_d G' i j f) (hg : It_map_d G' j k g) (hv : It_map_d G' i k v)
      x y z (hxy : Rd_entry_d x y f) (hyz : Rd_entry_d y z g) : Rd_entry_d x z v := by
    rcases (gs j k g).mp hg with hg | ⟨rfl, ⟨rfl, rfl⟩ | hg⟩
    · obtain ⟨hj, hk⟩ := h.order.bound j k (h.map_bound_l hZF hg)
      exact h.comp i j k f g v ((gold i j f hj).mp hf) hg ((gold i k v hk).mp hv) x y z hxy hyz
    · have eq := it_finish_unique_l hZF h b.subset cone ((gs i _ f).mp hf) ((gs i _ v).mp hv)
      exact eq ▸ ((es y z).mp hyz).2 ▸ hxy
    · have hf₀ := (gold i j f (b.subset j ((cone.domain j).mpr ⟨g, hg⟩))).mp hf
      rcases (gs i _ v).mp hv with hv | ⟨_, ⟨rfl, _⟩ | hv⟩
      · exact (no (h.order.bound i _ (h.map_bound_l hZF hv)).2).elim
      · exact (no (h.order.bound _ j (h.map_bound_l hZF hf₀)).1).elim
      · exact cone.commute i j f v g hf₀ hv hg x y z hxy hyz
  exact ⟨β, U, Q', G', e, hβ, ⟨order, qf.2.1, qf.2.2, fun i c hc => by
      rcases (qs i c).mp hc with hc | ⟨_, rfl⟩
      · exact h.models i c hc
      · exact ⟨N, W, cone.model⟩,
    gf, gd, typed, ident, commute⟩, us, qs, gs⟩

end YesMetaZFC.SetTheory.LargeCardinal
