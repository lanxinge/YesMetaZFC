import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Internal.Theory

/-! # 中间坐标的实际集合公式

编译 A={vᵢ | i<n, i≠e}，同时检验两个包含方向。A 是原节点中的函数图，
这里只绑定它，不把全部游戏坐标打成一个额外的高秩自由参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sg_set_d (e n f A : M.Domain) : Prop := ∀ x,
  M.mem x A ↔ ∃ i, M.mem i n ∧ i ≠ e ∧ M.PairMember I i x f

def sg_set_m {d} (e n f A : Term d) : Formula 1 d := set[d] ⟪∀ x, x ∈ ⌜A⌝ₛ ↔
  (∃ i ∈ ⌜n⌝ₛ, ¬ (i = ⌜e⌝ₛ) ∧ ⌜Formula.orderedPairMem 𝒞⌝ₚ(i, x, ⌜f⌝ₛ))⟫
derive_free_closed sg_set_m

theorem sg_set_sat_l (hE : Extensional M) {d} (ρ : Env M d) (e n f A : Term d) :
    Formula.satisfies ρ (sg_set_m (𝒞 := 𝒞) e n f A) ↔
      Sg_set_d I (e.eval ρ) (n.eval ρ) (f.eval ρ) (A.eval ρ) := by
  simp only [sg_set_m, Sg_set_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem sg_set_build_l (hZF : M.Models ZF) {ω e n b p : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (hb : M.mem b ω) (hp : M.mem p ω)
    (hbp : M.mem b p) (np : M.MemberSubset n p) :
    ∃ m G u, Sfm_d I ω m G ∧ M.mem u m ∧ ∀ c X R E f A,
      Smem_d I c X R → M.TransitiveSet X → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I b A f → (Ssat_d I X R E G m u f ↔ Sg_set_d I e n f A) := by
  obtain ⟨m₀, G₀, u₀, prog, root, any⟩ := sg_any_build_l I hZF (e := e) hω hp hn
  obtain ⟨m₁, G₁, add, rel⟩ := sfm_rel_l I hZF hω prog hp hb
  obtain ⟨m₂, G₂, u₂, iff, both⟩ := sfm_iff_l I hZF hω add.program add.root (add.span u₀ root)
  obtain ⟨m, G, u, all, quant⟩ := sfm_all_l I hZF hω iff.program hp iff.root
  refine ⟨m, G, u, all.program, all.root, fun c X R E f A model trans hE hf ha => ?_⟩
  have fn := (hE f).mp hf
  have hA := fn.output_mem_of_pairMember ha
  have body x g (hx : M.mem x X) (update : Senv_update_d I f p x g) :
      Ssat_d I X R E G₂ m₂ u₂ g ↔
        (M.mem x A ↔ ∃ i, M.mem i n ∧ i ≠ e ∧ M.PairMember I i x f) := by
    have hg := (hE g).mpr (update.function_l I fn hp hx)
    have px := (update.2 p x).mpr (Or.inl ⟨rfl, rfl⟩)
    have agree := update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    have bA := (agree b A hbp).mp ha
    have old := (add.sat_l I hZF prog root X R E g).symm.trans (any X R E g x hE hg px)
    have member : M.PairMember I x A R ↔ M.mem x A := (model.2 x A).trans
      ((and_iff_right hx).trans (and_iff_right hA))
    have entries : (∃ i, M.mem i n ∧ i ≠ e ∧ M.PairMember I i x g) ↔
        ∃ i, M.mem i n ∧ i ≠ e ∧ M.PairMember I i x f :=
      exists_congr fun i => and_congr_right fun hi => and_congr_right fun _ => (agree i x (np i hi)).symm
    exact (both X R E g hg).trans (iff_congr ((rel X R E g x A hE hg px bA).trans member) (old.trans entries))
  refine (quant X R E f hE hf).trans ⟨?_, ?_⟩
  · intro all x
    by_cases hx : M.mem x X
    · obtain ⟨g, update, _⟩ := senv_update_exists_l I hZF fn hp hx
      exact (body x g hx update).mp (all x g hx update)
    · exact iff_of_false (fun h => hx (trans A hA x h))
        (fun ⟨_, _, _, h⟩ => hx (fn.output_mem_of_pairMember h))
  · exact fun all x g hx update => (body x g hx update).mpr (all x)

end YesMetaZFC.SetTheory.Internal
