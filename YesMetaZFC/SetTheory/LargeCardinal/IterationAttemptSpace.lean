import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptNode
import YesMetaZFC.SetTheory.Collapse.RelationSequence

/-! # 联合尝试的实际节点集与严格扩展关系

有限行属于既有有限序列空间，行图属于其与 ω 的积的幂集。
据此用分离得到全部节点；严格扩展反向存为下降关系，供内部良基秩使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ja_cell_d (ω T Q G E Y W z π s : M.Domain) : Prop :=
  ∃ k P, KPair_d M s k P ∧ Ja_node_d I ω T Q G E Y W z π k P

def ja_cell_m {d} (ω T Q G E Y W z π s : Term d) : Formula 1 d := set[d] ⟪
  ∃ k P, ⌜kpair0_m⌝ₚ(⌜s⌝ₛ, k, P) ∧
    ⌜ja_node_m⌝ₚ(⌜ω⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜E⌝ₛ, ⌜Y⌝ₛ, ⌜W⌝ₛ, ⌜z⌝ₛ, ⌜π⌝ₛ, k, P)⟫
derive_free_closed ja_cell_m

theorem ja_cell_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω T Q G E Y W z π s : Term d)
    (hω : M.IsOmega (ω.eval ρ)) :
    Formula.satisfies ρ (ja_cell_m ω T Q G E Y W z π s) ↔
      Ja_cell_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (T.eval ρ) (Q.eval ρ) (G.eval ρ) (E.eval ρ) (Y.eval ρ) (W.eval ρ)
        (z.eval ρ) (π.eval ρ) (s.eval ρ) := by
  simp only [ja_cell_m, Ja_cell_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hZF.1, ja_node_sat_l hZF, Definitional.Term.eval_weaken, hω]; rfl

structure Ja_space_d (ω T Q G E Y W z π A R : M.Domain) : Prop where
  nodes : ∀ s, M.mem s A ↔ Ja_cell_d I ω T Q G E Y W z π s
  relation : M.IsSetRelation I R
  edges : ∀ s t, Rd_entry_d t s R ↔ M.mem s A ∧ M.mem t A ∧ Ja_extend_d T s t

variable (hZF : M.Models ZF)
local notation "I₀" => kp_pair_l (ZF.modelsKP hZF)

theorem Ja_space_d.node_l {ω T Q G E Y W z π A R s k P : M.Domain}
    (h : Ja_space_d I₀ ω T Q G E Y W z π A R) (hs : M.mem s A) (hp : KPair_d M s k P) :
    Ja_node_d I₀ ω T Q G E Y W z π k P := by
  obtain ⟨l, Q', hq, node⟩ := (h.nodes s).mp hs
  obtain ⟨el, eq⟩ := kpair_injective_l M hq hp
  subst l Q'
  exact node

theorem Ja_extend_d.read_l {T s t k P l Q : M.Domain} (e : Ja_extend_d T s t)
    (hs : KPair_d M s k P) (ht : KPair_d M t l Q) : M.mem k l ∧ Rd_entry_d k l T ∧
      ∀ i p q, Rd_entry_d i p P → Rd_entry_d i q Q → M.MemberSubset p q := by
  obtain ⟨k', P', l', Q', hs', ht', hk, hr, sub⟩ := e
  obtain ⟨ek, ep⟩ := kpair_injective_l M hs' hs
  obtain ⟨el, eq⟩ := kpair_injective_l M ht' ht
  subst k' P' l' Q'
  exact ⟨hk, hr, sub⟩

theorem ja_space_l {ω T Q G E Y W z π : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω ω T Q G) (en : Ja_enum_d I₀ ω ω Q E) :
    ∃ A R, Ja_space_d I₀ ω T Q G E Y W z π A R := by
  obtain ⟨S, hs⟩ := ZF.fseq_space_exists_l I₀ hZF hω Y
  obtain ⟨D, hd⟩ := ZF.exists_cartesianProduct hZF I₀ ω S
  obtain ⟨V, hv⟩ := ZF.exists_powerSet hZF D
  obtain ⟨U, hu⟩ := ZF.exists_cartesianProduct hZF I₀ ω V
  let φ : UnarySchema 9 := { body := (ja_cell_m (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) .newest) }
  let ρ : Env M 9 := ⟨Fin.cases ω (Fin.cases T (Fin.cases Q (Fin.cases G (Fin.cases E
    (Fin.cases Y (Fin.cases W (Fin.cases z (fun _ => π)))))))), fun _ => ω⟩
  have sat s : φ.denote ρ s ↔ Ja_cell_d I₀ ω T Q G E Y W z π s := ja_cell_sat_l hZF _ _ _ _ _ _ _ _ _ _ _ hω
  have bound s (snode : Ja_cell_d I₀ ω T Q G E Y W z π s) : M.mem s U := by
    obtain ⟨k, P, hp, node⟩ := snode
    refine (hu s).mpr ⟨k, node.length, P, (hv P).mpr ?_, hp⟩
    intro r hr
    obtain ⟨i, p, hi⟩ := node.function.1 r hr
    have hip : Rd_entry_d i p P := ⟨r, hi, hr⟩
    have hiω := (h.order.bound i k ((node.domain i).mp ⟨p, hip⟩)).1
    obtain ⟨c, X, R, hc, mx⟩ := h.model_l hZF hiω
    obtain ⟨e, he⟩ := (en.domain i).mp hiω
    exact (hd r).mpr ⟨i, hiω, p, (hs p).mpr ⟨k, node.length,
      fn0_function_l (ZF.modelsKP hZF) (node.rows i p c X R e hip hc mx.1 he).1⟩, hi⟩
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF φ ρ U
  have nodes s : M.mem s A ↔ Ja_cell_d I₀ ω T Q G E Y W z π s :=
    (ha s).trans ⟨fun h => (sat s).mp h.2, fun h => ⟨bound s h, (sat s).mpr h⟩⟩
  let ψ : BinarySchema 1 := { body := ja_extend_m (.bound 2) .newest (.bound 1) }
  obtain ⟨R, hr, rs⟩ := ZF.exists_setRelationOn_of_denote hZF I₀ ψ ⟨fun _ => T, fun _ => T⟩ A
  exact ⟨A, R, nodes, hr.1, fun s t => (rs t s).trans
    ⟨fun h => ⟨h.2.1, h.1, (ja_extend_sat_l hZF.1 ..).mp h.2.2⟩,
      fun h => ⟨h.2.1, h.1, (ja_extend_sat_l hZF.1 ..).mpr h.2.2⟩⟩⟩

/-- 扩展的传递性同时使用树序传递性与中间节点的全部前驱行。 -/
theorem ja_extend_trans_l {ω T Q G E Y W z π s t u : M.Domain} (h : It_order_d ω T)
    (ns : Ja_cell_d I₀ ω T Q G E Y W z π s) (nt : Ja_cell_d I₀ ω T Q G E Y W z π t)
    (nu : Ja_cell_d I₀ ω T Q G E Y W z π u) (st : Ja_extend_d T s t) (tu : Ja_extend_d T t u) : Ja_extend_d T s u := by
  obtain ⟨k, P, hp, np⟩ := ns
  obtain ⟨l, Q', hq, nq⟩ := nt
  obtain ⟨m, V, hv, nv⟩ := nu
  obtain ⟨k', P', l', Q'', hp', hq', hkl, ktl, sub⟩ := st
  obtain ⟨ek, ep⟩ := kpair_injective_l M hp' hp
  obtain ⟨el, eq⟩ := kpair_injective_l M hq' hq
  subst k' P' l' Q''
  obtain ⟨l', Q'', m', V', hq', hv', hlm, ltm, sub'⟩ := tu
  obtain ⟨el, eq⟩ := kpair_injective_l M hq' hq
  obtain ⟨em, ev⟩ := kpair_injective_l M hv' hv
  subst l' Q'' m' V'
  refine ⟨k, P, m, V, hp, hv, (h.ordinal.mem nv.length).transitive l hlm k hkl,
    h.trans k l m ktl ltm, fun i p r hip hir => ?_⟩
  obtain ⟨q, hiq⟩ := (nq.domain i).mpr (h.trans i k l ((np.domain i).mp ⟨p, hip⟩) ktl)
  exact fun x hx => sub' i q r hiq hir x (sub i p q hip hiq x hx)

end YesMetaZFC.SetTheory.LargeCardinal
