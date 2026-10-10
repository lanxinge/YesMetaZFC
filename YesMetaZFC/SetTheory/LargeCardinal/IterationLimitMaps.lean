import YesMetaZFC.SetTheory.LargeCardinal.IterationLimitModel
import YesMetaZFC.SetTheory.LargeCardinal.IterationLimitOrder

/-! # 极限处新增的整列嵌入图

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
    (h : It_diagram_d hZF ω α T Q G) (inside : M.MemberSubset B α) (cone : It_cone_d hZF ω B Q G d N W P)
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
    (h : It_diagram_d hZF ω α T Q G) (inside : M.MemberSubset B α) (cone : It_cone_d hZF ω B Q G d N W P)
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
