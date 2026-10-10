import YesMetaZFC.SetTheory.Collapse.RelationSyntax

/-! # 有集合值域界的内部良基递归

算子是实际三元原公式：附加参数为前驱值图，两个主变量为节点和值。
只要求算子在前驱值确定时全定义且唯一；后续 Borel 码装配提供具体实例。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def wop_m {n d} (φ : BinarySchema (n+1)) (e : Definitional.TermVector n d) (G a c : Term d) : Formula 1 d :=
  Formula.related φ (Definitional.TermVector.ofFn (Fin.cases G e)) a c
@[simp] theorem wop_closed_l {n d} (φ : BinarySchema (n+1)) (e : Definitional.TermVector n d) (G a c : Term d)
    (he : e.FreeClosed) (hG : G.freeSupport = []) (ha : a.freeSupport = []) (hc : c.freeSupport = []) :
    (wop_m φ e G a c).FreeClosed := by
  apply Formula.related_freeClosed_of_closed _ _ _ _ ?_ ha hc
  intro i
  cases i using Fin.cases <;> simp only [Definitional.TermVector.get_ofFn, Fin.cases_zero, Fin.cases_succ]
  · exact hG
  · exact he _

theorem wop_sat_l {n d} (φ : BinarySchema (n+1)) (e : Definitional.TermVector n d) (ρ : Env M d) (G a c : Term d) :
    Formula.satisfies ρ (wop_m φ e G a c) ↔ φ.denote ((e.evalEnv ρ).push (G.eval ρ)) (a.eval ρ) (c.eval ρ) := by
  rw [wop_m, Formula.satisfies_related_iff]
  have h : (Definitional.TermVector.ofFn (Fin.cases G e)).evalEnv ρ = (e.evalEnv ρ).push (G.eval ρ) := by
    unfold Definitional.TermVector.evalEnv Env.push
    congr 1
    funext i
    cases i using Fin.cases <;> simp [Definitional.TermVector.eval]
  rw [h]

def Wfr_d {n} (φ : BinarySchema (n+1)) (ρ : Env M n) (X R Y G : M.Domain) : Prop := M.IsSetFunction I G ∧
  ∀ a c, M.PairMember I a c G → M.mem a X ∧ M.mem c Y ∧
    (∀ b, M.mem b X → Rd_entry_d b a R → ∃ d, M.PairMember I b d G) ∧ φ.denote (ρ.push G) a c
def wfr_m {n d} (φ : BinarySchema (n+1)) (e : Definitional.TermVector n d) (X R Y G : Term d) : Formula 1 d :=
  .conj (Formula.isFunction 𝒞 G) (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken)
    (.conj (.mem (.bound 1) X.weaken.weaken) (.conj (.mem .newest Y.weaken.weaken) (.conj
      (Formula.forallMem X.weaken.weaken (.imp (rd_entry_m .newest (.bound 2) R.weaken.weaken.weaken)
        (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken.weaken.weaken))))
      (wop_m φ e.weaken.weaken G.weaken.weaken (.bound 1) .newest)))))))
derive_free_closed wfr_m
theorem wfr_sat_l (hE : Extensional M) {n d} (φ : BinarySchema (n+1)) (e : Definitional.TermVector n d)
    (ρ : Env M d) (X R Y G : Term d) : Formula.satisfies ρ (wfr_m (𝒞 := 𝒞) φ e X R Y G) ↔
      Wfr_d I φ (e.evalEnv ρ) (X.eval ρ) (R.eval ρ) (Y.eval ρ) (G.eval ρ) := by
  simp only [wfr_m, Wfr_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, rd_entry_sat_l hE,
    Formula.satisfies_exists_iff, wop_sat_l, Definitional.TermVector.evalEnv_weaken, Definitional.Term.eval_weaken]; rfl

theorem wfr_agree_l (hZF : M.Models ZF) {n} {φ : BinarySchema (n+1)} {ρ : Env M n} {X R Y G H}
    (hw : Wf_rel_d X R)
    (hu : ∀ a G H c d, M.mem a X → M.IsSetFunction I G → M.IsSetFunction I H →
      (∀ b v, M.mem b X → Rd_entry_d b a R → (M.PairMember I b v G ↔ M.PairMember I b v H)) →
      φ.denote (ρ.push G) a c → φ.denote (ρ.push H) a d → c = d)
    (hG : Wfr_d I φ ρ X R Y G) (hH : Wfr_d I φ ρ X R Y H) :
    ∀ a c d, M.PairMember I a c G → M.PairMember I a d H → c = d := by
  let η : Env M 2 := (⟨fun _ => G, fun _ => G⟩ : Env M 1).push H
  let ψ : UnarySchema 2 := { body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4)) (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (Formula.extensionalEq (.bound 1) .newest)))) }
  have hp a : ψ.denote η a ↔ ∀ c d, M.PairMember I a c G → M.PairMember I a d H → c = d := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all := wf_rel_ind_l hZF hw ψ η (fun a ha ih => (hp a).mpr (by
    intro c d hc hd
    apply hu a G H c d ha hG.1 hH.1 ?_ (hG.2 a c hc).2.2.2 (hH.2 a d hd).2.2.2
    intro b v hb hr
    obtain ⟨x, hx⟩ := (hG.2 a c hc).2.2.1 b hb hr
    obtain ⟨y, hy⟩ := (hH.2 a d hd).2.2.1 b hb hr
    exact ⟨fun hv => ((hp b).mp (ih b hb hr) v y hv hy).symm ▸ hy,
      fun hv => (hp b).mp (ih b hb hr) x v hx hv ▸ hx⟩))
  exact fun a c d hc hd => (hp a).mp (all a (hG.2 a c hc).1) c d hc hd

end YesMetaZFC.SetTheory
